use std::time::Duration;

use crate::lifecycle::{self, confirmation_deadline, MembershipRecord, MembershipState};
use crate::path_cache;
use crate::provider::{backend_for, ProviderMembership, Registry};
use crate::registry_id;
use crate::sealed_store::store as sealed;
use crate::worker;

const TICK: Duration = Duration::from_secs(15);
const REFRESH_EVERY: u32 = 4;

pub(crate) fn ensure_running() {
    worker::ensure(worker::Slot::Poller, "rln-poller", run_loop);
}

pub(crate) fn run_loop(my_gen: u64) {
    let mut tick_no: u32 = 0;
    loop {
        if !worker::wait_tick(my_gen, TICK) {
            return;
        }
        tick_no = tick_no.wrapping_add(1);
        let refresh = tick_no.is_multiple_of(REFRESH_EVERY);
        tick(refresh);
    }
}

fn observe(record: &MembershipRecord) -> Option<Option<ProviderMembership>> {
    let registry = match registry_id::parse(&record.identity.registry_id) {
        Ok(r) => r,
        Err(e) => {
            eprintln!(
                "membership poller: bad stored registry_id {}: {e}",
                record.identity.registry_id
            );
            return None;
        }
    };
    observe_with(
        record,
        &registry,
        backend_for(&registry.namespace)?.registry,
    )
}

fn observe_with(
    record: &MembershipRecord,
    registry: &registry_id::CanonicalRegistryId,
    source: &dyn Registry,
) -> Option<Option<ProviderMembership>> {
    match source.get_membership(registry, &record.identity.identity_commitment) {
        Ok(pm) => Some(pm),
        Err(e) => {
            eprintln!(
                "membership poller: {} read failed: {}",
                record.identity.registry_id, e.message
            );
            None
        }
    }
}

pub(crate) fn absent_verdict(record: &MembershipRecord) -> (MembershipState, &'static str) {
    if record.cache.state == MembershipState::Unknown && record.cache.first_active_at.is_none() {
        (MembershipState::Failed, "not_on_registry")
    } else {
        (MembershipState::Erased, "removed_from_registry")
    }
}

pub(crate) fn write_if_still(
    hash: &str,
    expected: MembershipState,
    f: impl FnOnce(&mut lifecycle::CacheState),
) -> Result<Option<MembershipState>, crate::error::ApiError> {
    let prior = sealed::current_or_uninit()?.update_cache(hash, |m| {
        if m.state == expected {
            f(m);
        }
    })?;
    Ok((prior == expected).then_some(prior))
}

fn apply_observed(
    hash: &str,
    expected: MembershipState,
    pm: &ProviderMembership,
) -> Result<Option<MembershipState>, crate::error::ApiError> {
    write_if_still(hash, expected, |m| {
        m.state = pm.state;
        if let Some(l) = pm.leaf_index {
            m.leaf_index = Some(l);
        }
        m.rate_limit = Some(pm.rate_limit);
        m.failed_reason = None;
        m.retryable = None;
    })
}

fn tick(refresh_states: bool) {
    if crate::worker::is_stopped() {
        return;
    }
    let pending = match sealed::current() {
        Some(store) => store.pending_records(),
        None => return,
    };
    let now = crate::util::now_unix();
    for record in pending {
        let hash = &record.hash;
        let expected = record.cache.state;
        match observe(&record) {
            Some(Some(pm)) => match apply_observed(hash, expected, &pm) {
                Err(e) => {
                    eprintln!("membership poller: confirm update failed: {}", e.message)
                }
                Ok(Some(prior)) => {
                    lifecycle::emit_transition(hash, &record, prior, pm.state);
                    eprintln!(
                        "membership poller: {hash} confirmed {:?} at leaf {:?}",
                        pm.state, pm.leaf_index
                    )
                }
                Ok(None) => {}
            },
            Some(None) if now > confirmation_deadline(&record) => {
                let result = write_if_still(hash, expected, |m| {
                    m.state = MembershipState::Failed;
                    m.failed_reason = Some("confirmation_window_elapsed".to_string());
                    m.retryable = Some(true);
                });
                match result {
                    Err(e) => eprintln!("membership poller: fail update failed: {}", e.message),
                    Ok(Some(prior)) => {
                        crate::lifecycle::forget_granted_by(hash);
                        lifecycle::emit_transition(hash, &record, prior, MembershipState::Failed);
                        eprintln!("membership poller: {hash} failed (window elapsed)");
                    }
                    Ok(None) => {}
                }
            }
            _ => {}
        }
    }

    if !refresh_states {
        return;
    }
    let refreshable = match sealed::current() {
        Some(store) => store.refreshable_records(),
        None => return,
    };
    for record in refreshable {
        let hash = &record.hash;
        let expected = record.cache.state;
        match observe(&record) {
            Some(Some(pm)) => {
                if let Ok(Some(prior)) = apply_observed(hash, expected, &pm) {
                    lifecycle::emit_transition(hash, &record, prior, pm.state);
                }
            }
            Some(None) => {
                let (state, reason) = absent_verdict(&record);
                let updated = write_if_still(hash, expected, |m| {
                    m.state = state;
                    m.failed_reason = Some(reason.to_string());
                    if state == MembershipState::Failed {
                        m.retryable = Some(true);
                    }
                });
                if let Ok(Some(prior)) = updated {
                    crate::lifecycle::forget_granted_by(hash);
                    lifecycle::emit_transition(hash, &record, prior, state);
                    eprintln!("membership poller: {hash} not on the registry — {reason}");
                }
            }
            None => {}
        }
    }

    refresh_paths();
}

pub(crate) fn refresh_paths() {
    if crate::worker::is_stopped() {
        return;
    }
    let Some(store) = sealed::current() else {
        return;
    };
    let usable = store.refreshable_records();
    for record in usable.into_iter().filter(|r| r.cache.state.is_usable()) {
        let hash = &record.hash;
        let registry = match registry_id::parse(&record.identity.registry_id) {
            Ok(r) => r,
            Err(e) => {
                eprintln!(
                    "membership poller: bad stored registry_id {}: {e}",
                    record.identity.registry_id
                );
                continue;
            }
        };
        let Some(backend) = backend_for(&registry.namespace) else {
            continue;
        };
        let Some(leaf_index) = record.cache.leaf_index else {
            eprintln!("membership poller: {hash} is usable but carries no leaf_index — path refresh skipped");
            continue;
        };
        let prepared = match path_cache::fetch_path(&registry, hash, leaf_index, backend.tree) {
            Ok(prepared) => prepared,
            Err(e) => {
                eprintln!(
                    "membership poller: {hash} path refresh failed: {}",
                    e.message
                );
                if crate::worker::is_stopped() {
                    return;
                }
                continue;
            }
        };
        // Build the partial for the new path before that path is visible, so
        // proofs keep hitting the previous (still valid) partial during the
        // build. A skip or a failure still publishes the path.
        if !crate::worker::is_stopped() {
            let rate_limit = record.cache.rate_limit.unwrap_or(0);
            match crate::proof_api::warm_prepared(&store, hash, rate_limit, &prepared) {
                Ok(true) => eprintln!("membership poller: {hash} partial proof rebuilt"),
                Ok(false) => {}
                Err(e) => eprintln!(
                    "membership poller: {hash} partial proof rebuild failed: {}",
                    e.message
                ),
            }
        }
        path_cache::publish_path(hash, prepared);
        if crate::worker::is_stopped() {
            return;
        }
    }
    log_partial_stats();
}

/// One line per poll cycle in which the partial-proof counters moved, so an
/// operator can see the cache working (mostly hits) or not (misses, fallbacks).
fn log_partial_stats() {
    static LAST: std::sync::Mutex<crate::proof::PartialStats> =
        std::sync::Mutex::new(crate::proof::PartialStats {
            hits: 0,
            misses: 0,
            refreshes: 0,
            fallbacks: 0,
        });
    let now = crate::proof::partial_stats();
    let mut last = crate::lock(&LAST);
    if *last != now {
        eprintln!(
            "rln proof: partial-proof cache hits={} misses={} refreshes={} fallbacks={}",
            now.hits, now.misses, now.refreshes, now.fallbacks
        );
        *last = now;
    }
}

#[cfg(test)]
mod tests {
    use crate::lifecycle::MembershipState;
    use crate::poller;
    use crate::test_support::{imp_with_store, seed_membership, TEST_GLOBAL_LOCK};

    #[test]
    fn a_pending_record_is_confirmed_through_the_registry() {
        use crate::provider::fake::{self, FakePayer, FakeRegistry, FakeTree};
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        let dir =
            std::env::temp_dir().join(format!("rln-poller-confirm-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let (_imp, store) = imp_with_store(dir.clone());
        store.unlock("pw").unwrap();
        let registry = "fakens:local:confirm";
        seed_membership(
            &store,
            "conf",
            registry,
            &"56".repeat(32),
            "",
            &"e6".repeat(32),
            MembershipState::Pending,
            0,
            100,
        );
        store.update_cache("conf", |m| m.leaf_index = None).unwrap();

        let install = |leaf: Option<u64>| {
            crate::test_support::install_backend(fake::backend(
                FakeTree::default(),
                FakeRegistry {
                    membership: Some(Some((MembershipState::Active, leaf, 100))),
                    bounds: None,
                },
                FakePayer::default(),
            ))
        };
        install(Some(4));
        poller::tick(false);
        let rec = store.membership("conf").unwrap();
        assert_eq!(
            (rec.cache.state, rec.cache.leaf_index),
            (MembershipState::Active, Some(4))
        );

        install(None);
        store
            .update_cache("conf", |m| m.state = MembershipState::Pending)
            .unwrap();
        poller::tick(false);
        let rec = store.membership("conf").unwrap();
        assert_eq!(
            (rec.cache.state, rec.cache.leaf_index),
            (MembershipState::Active, Some(4))
        );

        crate::sealed_store::store::publish(None);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn a_tree_change_rebuilds_the_partial_proof_and_an_unchanged_tree_keeps_it() {
        use crate::proof;
        use crate::provider::fake::{self, FakePayer, FakeRegistry, FakeTree};
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        let dir =
            std::env::temp_dir().join(format!("rln-poller-partial-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let (_imp, store) = imp_with_store(dir.clone());
        store.unlock("pw").unwrap();
        let registry = "fakens:local:partial";
        let hash = "poller-partial-slot";
        // A secret that is a canonical field element (LE 1), so it can prove.
        let secret = format!("01{}", "00".repeat(31));
        seed_membership(
            &store,
            hash,
            registry,
            &"57".repeat(32),
            "",
            &secret,
            MembershipState::Active,
            3,
            100,
        );

        // The tree as the provider reports it: only the sibling at level 0
        // differs between the two snapshots, like another member registering.
        let install = |sibling: &str| {
            crate::test_support::install_backend(fake::backend(
                FakeTree {
                    proof: Some(serde_json::json!({
                        "depth": 2, "leaf": "aa".repeat(32), "leaf_index": 3,
                        "path_elements": [sibling, "00".repeat(32)], "path_indices": [1, 1],
                        "root": "bb".repeat(32),
                    })),
                    roots: None,
                },
                FakeRegistry {
                    membership: Some(Some((MembershipState::Active, Some(3), 100))),
                    bounds: None,
                },
                FakePayer::default(),
            ))
        };

        install(&"00".repeat(32));
        poller::refresh_paths();
        let first = proof::partial_slot_fingerprint(hash).expect("poller built the partial");
        assert_eq!(proof::partial_hits(hash), Some(0));

        proof::touch_partial_for_test(hash);
        poller::refresh_paths();
        assert_eq!(proof::partial_slot_fingerprint(hash), Some(first));
        assert_eq!(
            proof::partial_hits(hash),
            Some(1),
            "an unchanged tree keeps the slot (no rebuild)"
        );

        install(&format!("02{}", "00".repeat(31)));
        poller::refresh_paths();
        let second = proof::partial_slot_fingerprint(hash).expect("slot after tree change");
        assert_ne!(second, first, "the tree change reached the slot");
        assert_eq!(
            proof::partial_hits(hash),
            Some(0),
            "the poller rebuilt the partial for the new path"
        );

        crate::sealed_store::store::publish(None);
        let _ = std::fs::remove_dir_all(&dir);
    }

    fn install_partial_tree(sibling: &str, state: MembershipState) {
        use crate::provider::fake::{self, FakePayer, FakeRegistry, FakeTree};
        crate::test_support::install_backend(fake::backend(
            FakeTree {
                proof: Some(serde_json::json!({
                    "depth": 2, "leaf": "aa".repeat(32), "leaf_index": 3,
                    "path_elements": [sibling, "00".repeat(32)], "path_indices": [1, 1],
                    "root": "bb".repeat(32),
                })),
                roots: None,
            },
            FakeRegistry {
                membership: Some(Some((state, Some(3), 100))),
                bounds: None,
            },
            FakePayer::default(),
        ));
    }

    #[test]
    fn a_locked_keystore_skips_the_partial_rebuild() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        let dir =
            std::env::temp_dir().join(format!("rln-poller-locked-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let (_imp, store) = imp_with_store(dir.clone());
        store.unlock("pw").unwrap();
        let hash = "poller-locked-slot";
        seed_membership(
            &store,
            hash,
            "fakens:local:locked",
            &"58".repeat(32),
            "",
            &format!("01{}", "00".repeat(31)),
            MembershipState::Active,
            3,
            100,
        );
        install_partial_tree(&"00".repeat(32), MembershipState::Active);
        store.lock();

        poller::refresh_paths();
        assert!(
            crate::path_cache::hit(hash, 3).is_some(),
            "a locked keystore still publishes the refreshed path"
        );
        assert_eq!(
            crate::proof::partial_slot_fingerprint(hash),
            None,
            "a locked keystore builds no partial"
        );

        crate::sealed_store::store::publish(None);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn locking_or_closing_the_keystore_drops_only_that_stores_partials() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        let dir =
            std::env::temp_dir().join(format!("rln-poller-evict-lock-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let (_imp, store) = imp_with_store(dir.clone());
        store.unlock("pw").unwrap();
        let hash = "poller-evict-lock-slot";
        let bystander = "poller-evict-lock-bystander";
        seed_membership(
            &store,
            hash,
            "fakens:local:evictlock",
            &"59".repeat(32),
            "",
            &format!("01{}", "00".repeat(31)),
            MembershipState::Active,
            3,
            100,
        );
        install_partial_tree(&"00".repeat(32), MembershipState::Active);
        poller::refresh_paths();
        assert!(crate::proof::partial_slot_fingerprint(hash).is_some());
        crate::proof::clone_slot_for_test(hash, bystander);

        store.lock();
        assert_eq!(
            crate::proof::partial_slot_fingerprint(hash),
            None,
            "lock drops the store's partial"
        );
        assert!(
            crate::proof::partial_slot_fingerprint(bystander).is_some(),
            "lock leaves slots that are not this store's"
        );

        crate::proof::clone_slot_for_test(bystander, hash);
        store.close();
        assert_eq!(
            crate::proof::partial_slot_fingerprint(hash),
            None,
            "close drops the store's partial"
        );
        assert!(crate::proof::partial_slot_fingerprint(bystander).is_some());

        crate::sealed_store::store::publish(None);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn leaving_the_usable_states_drops_only_that_partial() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        let dir =
            std::env::temp_dir().join(format!("rln-poller-evict-state-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let (_imp, store) = imp_with_store(dir.clone());
        store.unlock("pw").unwrap();
        let hash = "poller-evict-state-slot";
        let bystander = "poller-evict-state-bystander";
        seed_membership(
            &store,
            hash,
            "fakens:local:evictstate",
            &"5a".repeat(32),
            "",
            &format!("01{}", "00".repeat(31)),
            MembershipState::Active,
            3,
            100,
        );
        install_partial_tree(&"00".repeat(32), MembershipState::Active);
        poller::refresh_paths();
        let fingerprint = crate::proof::partial_slot_fingerprint(hash).expect("warmed");
        crate::proof::clone_slot_for_test(hash, bystander);

        install_partial_tree(&"00".repeat(32), MembershipState::Expired);
        poller::tick(true);
        assert_eq!(
            store.membership(hash).unwrap().cache.state,
            MembershipState::Expired
        );
        assert_eq!(
            crate::proof::partial_slot_fingerprint(hash),
            None,
            "leaving usable drops the partial, got {fingerprint:?}"
        );
        assert!(
            crate::proof::partial_slot_fingerprint(bystander).is_some(),
            "another membership's slot stays"
        );

        crate::sealed_store::store::publish(None);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn an_absent_record_is_erased_only_if_it_was_ever_on_the_registry() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        let dir =
            std::env::temp_dir().join(format!("rln-absent-verdict-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let (_imp, store) = imp_with_store(dir.clone());
        store.unlock("pw").unwrap();
        let registry = format!("logos:local:{}", "7c".repeat(32));
        seed_membership(
            &store,
            "was",
            &registry,
            &"54".repeat(32),
            "",
            &"e4".repeat(32),
            MembershipState::Active,
            1,
            100,
        );
        seed_membership(
            &store,
            "never",
            &registry,
            &"55".repeat(32),
            "",
            &"e5".repeat(32),
            MembershipState::Unknown,
            0,
            100,
        );
        assert_eq!(
            poller::absent_verdict(&store.membership("was").unwrap()),
            (MembershipState::Erased, "removed_from_registry")
        );
        assert_eq!(
            poller::absent_verdict(&store.membership("never").unwrap()),
            (MembershipState::Failed, "not_on_registry")
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
}
