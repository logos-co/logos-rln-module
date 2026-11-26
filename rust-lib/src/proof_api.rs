use std::sync::Arc;

use crate::config::epoch_params_for;
use crate::error::{ApiError, ErrorKind};
use crate::nullifier_log;
use crate::ok_json;
use crate::path_cache;
use crate::proof;
use crate::rate_limit;
use crate::registry_id;
use crate::roots;
use crate::scope::{backend_of, parse_scope, records_for_registry, scope_candidates};
use crate::sealed_store::store::Store;
use crate::select;
use crate::tree::TreeSource;
use crate::util::now_unix;
use crate::views;

pub(crate) fn proof_error(e: proof::ProofError) -> ApiError {
    match e {
        proof::ProofError::BadInput(m) => ApiError::new(ErrorKind::InvalidArgument, m),
        proof::ProofError::Engine(m) => ApiError::new(ErrorKind::Transient, m),
    }
}

pub(crate) fn generate_proof_impl(
    store: Result<Arc<Store>, ApiError>,
    registry_id_raw: &str,
    rln_identifier_hex: &str,
    signal_hex: &str,
    timestamp: &str,
) -> Result<serde_json::Value, ApiError> {
    generate_proof_with(
        store,
        registry_id_raw,
        rln_identifier_hex,
        SignalArg::Raw(signal_hex),
        timestamp,
    )
}

#[derive(Clone, Copy)]
pub(crate) enum SignalArg<'a> {
    Raw(&'a str),
    Prehashed(&'a str),
}

impl SignalArg<'_> {
    pub(crate) fn resolve(self) -> Result<rln_signal::Fr, ApiError> {
        match self {
            SignalArg::Raw(hex) => registry_id::hex_to_vec(hex)
                .map(|bytes| proof::signal_to_x(&bytes))
                .ok_or_else(|| ApiError::new(ErrorKind::InvalidArgument, "signal must be hex")),
            SignalArg::Prehashed(hex) => proof::x_from_hash_hex(hex).map_err(|_| {
                ApiError::new(
                    ErrorKind::InvalidArgument,
                    "signal_hash must be the 32-byte LE hex of a canonical field element",
                )
            }),
        }
    }
}

pub(crate) fn generate_proof_with(
    store: Result<Arc<Store>, ApiError>,
    registry_id_raw: &str,
    rln_identifier_hex: &str,
    signal: SignalArg<'_>,
    timestamp: &str,
) -> Result<serde_json::Value, ApiError> {
    let (registry, rln_identifier, rln_id_hex) = parse_scope(registry_id_raw, rln_identifier_hex)?;
    let backend = backend_of(&registry)?;
    let (epoch, size, gap, now_epoch) = fresh_epoch_for(&registry.canonical, timestamp)?;
    let x = signal.resolve()?;

    roots::track(&registry);

    let store = store?;
    let records = records_for_registry(&store, &registry);
    let candidates = scope_candidates(&records, &rln_id_hex);
    let selected = select::select(
        &candidates,
        (&registry.canonical, &rln_id_hex),
        &select::Selector::None,
    )?;
    let hash = selected.hash.as_str();
    let record = store.membership(hash).ok_or_else(|| {
        ApiError::new(ErrorKind::UnknownMembership, "selected membership vanished")
    })?;
    let leaf_index = record.cache.leaf_index.ok_or_else(|| {
        ApiError::new(
            ErrorKind::UnknownMembership,
            "the selected membership carries no leaf_index",
        )
    })?;
    let rate_limit = record.cache.rate_limit.unwrap_or(0);

    let eviction_mark = proof::eviction_mark(hash);
    let mut credential = store.unseal_credential(hash)?;

    let served = match path_cache::hit(hash, leaf_index) {
        Some(path) => path,
        None => {
            path_cache::fill_path_cache(&registry, hash, leaf_index, backend.tree)?;
            path_cache::hit(hash, leaf_index)
                .ok_or_else(|| ApiError::internal("path cache: fetched path vanished before use"))?
        }
    };
    // Before a message id is reserved: a cached root that has left the
    // accepted window is refreshed once, and still-stale is not_ready.
    let served = refresh_if_root_left_window(&registry, hash, leaf_index, backend.tree, served)?;

    let retain_floor = now_epoch.saturating_sub(gap);
    let message_id =
        store.reserve_message_id(hash, &rln_id_hex, epoch, retain_floor, rate_limit, size)?;

    let material = proof::WitnessMaterial {
        membership_hash: hash.to_string(),
        identity_secret_hash_hex: std::mem::take(&mut credential.identity_secret_hash),
        rate_limit,
        message_id,
        path_elements_hex: served.path_elements_hex,
        path_indices: served.path_indices,
        path_version: served.version,
        eviction_mark,
    };
    let rlp = proof::generate(&material, x, epoch, &rln_identifier).map_err(proof_error)?;

    let mut out = rlp.to_json();
    if let Some(obj) = out.as_object_mut() {
        obj.insert("message_id".to_string(), message_id.into());
        obj.insert("epoch_index".to_string(), epoch.into());
        obj.insert("membership_hash".to_string(), hash.into());
        obj.insert("proof_canonical".to_string(), rlp.canonical_hex().into());
    }
    Ok(out)
}

/// True when a warm window is known and does not contain `root`. No stored
/// root, or no window yet, keeps today's behaviour: prove with the path.
fn root_left_window(canonical: &str, root: Option<[u8; 32]>) -> bool {
    match root {
        Some(root) => roots::window(canonical).is_some_and(|window| !window.contains(&root)),
        None => false,
    }
}

/// Refill once when the cached root has left the accepted-root window, then
/// re-check the window `fill_path_cache` just published. Still outside: a
/// retryable error, and the caller has not reserved a message id.
fn refresh_if_root_left_window(
    registry: &registry_id::CanonicalRegistryId,
    hash: &str,
    leaf_index: u64,
    tree: &dyn TreeSource,
    mut served: path_cache::ServedPath,
) -> Result<path_cache::ServedPath, ApiError> {
    if !root_left_window(&registry.canonical, served.root) {
        return Ok(served);
    }
    path_cache::fill_path_cache(registry, hash, leaf_index, tree)?;
    served = path_cache::hit(hash, leaf_index)
        .ok_or_else(|| ApiError::internal("path cache: fetched path vanished before use"))?;
    if root_left_window(&registry.canonical, served.root) {
        return Err(ApiError::new(
            ErrorKind::NotReady,
            "membership root is outside the accepted-root window; retry",
        ));
    }
    Ok(served)
}

/// Rebuild a membership's cached partial proof for `path` when its fingerprint
/// changed, so the next `generate_proof` only finishes it. The fingerprint is
/// hashed once and passed through. A locked keystore is not an error (nothing
/// to warm). Returns whether a new partial was stored.
pub(crate) fn warm_prepared(
    store: &Store,
    hash: &str,
    rate_limit: u64,
    path: &path_cache::PreparedPath,
) -> Result<bool, ApiError> {
    if rate_limit == 0 {
        return Ok(false);
    }
    let fingerprint =
        proof::partial_fingerprint(rate_limit, &path.path_elements_hex, &path.path_indices);
    if proof::partial_matches(hash, &fingerprint) {
        // Already current: only advance the slot's generation. No unseal.
        proof::adopt_path_version(hash, &fingerprint, path.version);
        return Ok(false);
    }
    let eviction_mark = proof::eviction_mark(hash);
    let mut credential = match store.unseal_credential(hash) {
        Ok(credential) => credential,
        Err(e) if e.kind == ErrorKind::Locked => return Ok(false),
        Err(e) => return Err(e),
    };
    let material = proof::WitnessMaterial {
        membership_hash: hash.to_string(),
        identity_secret_hash_hex: std::mem::take(&mut credential.identity_secret_hash),
        rate_limit,
        message_id: 0,
        path_elements_hex: path.path_elements_hex.clone(),
        path_indices: path.path_indices.clone(),
        path_version: path.version,
        eviction_mark,
    };
    proof::warm_with_fingerprint(&material, fingerprint).map_err(proof_error)
}

pub(crate) fn epoch_of_timestamp(timestamp: &str, epoch_size_sec: u64) -> Result<u64, ApiError> {
    Ok(rate_limit::current_epoch(
        timestamp.trim().parse::<u64>().map_err(|_| {
            ApiError::new(
                ErrorKind::InvalidArgument,
                "timestamp must be a Unix-seconds integer",
            )
        })?,
        epoch_size_sec,
    ))
}

pub(crate) fn epoch_in_window(epoch: u64, now_epoch: u64, gap: u64) -> bool {
    (now_epoch.saturating_sub(gap)..=now_epoch.saturating_add(gap)).contains(&epoch)
}

pub(crate) fn fresh_epoch_for(
    registry: &str,
    timestamp: &str,
) -> Result<(u64, u64, u64, u64), ApiError> {
    let (size, gap) = epoch_params_for(registry)?;
    let epoch = epoch_of_timestamp(timestamp, size)?;
    let now_epoch = rate_limit::current_epoch(now_unix(), size);
    if !epoch_in_window(epoch, now_epoch, gap) {
        return Err(ApiError::new(
            ErrorKind::InvalidArgument,
            "timestamp is outside the acceptable epoch window (now ± max_epoch_gap)",
        ));
    }
    Ok((epoch, size, gap, now_epoch))
}

pub(crate) fn epoch_binding_holds(
    carried: Option<u64>,
    bound: &[u8; 32],
    rln_identifier: &[u8; 32],
    expected_epoch: u64,
    now_epoch: u64,
    gap: u64,
) -> bool {
    epoch_in_window(expected_epoch, now_epoch, gap)
        && carried.is_none_or(|e| e == expected_epoch)
        && proof::expected_external_nullifier(expected_epoch, rln_identifier) == *bound
}

pub(crate) fn validate_proof_impl(
    registry_id_raw: &str,
    rln_identifier_hex: &str,
    signal_hex: &str,
    timestamp: &str,
    proof_json: &str,
) -> Result<serde_json::Value, ApiError> {
    validate_proof_with(
        registry_id_raw,
        rln_identifier_hex,
        SignalArg::Raw(signal_hex),
        timestamp,
        proof_json,
    )
}

pub(crate) fn validate_proof_with(
    registry_id_raw: &str,
    rln_identifier_hex: &str,
    signal: SignalArg<'_>,
    timestamp: &str,
    proof_json: &str,
) -> Result<serde_json::Value, ApiError> {
    let (registry, rln_identifier, _) = parse_scope(registry_id_raw, rln_identifier_hex)?;
    backend_of(&registry)?;
    let (size, gap) = epoch_params_for(&registry.canonical)?;
    let now_epoch = rate_limit::current_epoch(now_unix(), size);
    let expected_epoch = epoch_of_timestamp(timestamp, size)?;
    let x = signal.resolve()?;
    let mut proof_value: serde_json::Value = serde_json::from_str(proof_json)
        .map_err(|e| ApiError::new(ErrorKind::InvalidArgument, format!("proof_json: {e}")))?;
    let derive_external_nullifier =
        proof_value.get("root").is_some() && proof_value.get("external_nullifier").is_none();
    if derive_external_nullifier {
        proof_value["external_nullifier"] = serde_json::Value::String(registry_id::bytes_to_hex(
            &proof::expected_external_nullifier(expected_epoch, &rln_identifier),
        ));
    }
    let rlp = proof::RateLimitProof::from_json(&proof_value).map_err(proof_error)?;

    let bound = rlp.external_nullifier();
    if !epoch_binding_holds(
        rlp.epoch(),
        &bound,
        &rln_identifier,
        expected_epoch,
        now_epoch,
        gap,
    ) {
        return ok_json(views::VerdictReply::verdict("invalid"));
    }

    roots::track(&registry);
    let window = roots::window(&registry.canonical).ok_or_else(|| {
        ApiError::new(ErrorKind::NotReady, "valid-root window not warm yet; retry")
    })?;
    if !window.contains(&rlp.root()) {
        roots::nudge();
        return ok_json(views::VerdictReply::verdict("invalid"));
    }
    if !proof::verify(&rlp, x, &window).map_err(proof_error)? {
        return ok_json(views::VerdictReply::verdict("invalid"));
    }

    let retain_floor = now_epoch.saturating_sub(gap);
    let view = match nullifier_log::record_verified(
        &registry.canonical,
        expected_epoch,
        rlp.nullifier(),
        rlp.share_x(),
        rlp.share_y(),
        retain_floor,
    ) {
        nullifier_log::RecordOutcome::Fresh => views::VerdictReply::verdict("valid"),
        nullifier_log::RecordOutcome::Duplicate => views::VerdictReply::verdict("duplicate"),
        nullifier_log::RecordOutcome::Collision { prior_x, prior_y } => {
            let recovered_secret = proof::recover_identity_secret_hex(
                (prior_x, prior_y),
                (rlp.share_x(), rlp.share_y()),
            )
            .map_err(proof_error)?;
            views::VerdictReply::rate_limit_violation(recovered_secret)
        }
    };
    let view = if derive_external_nullifier {
        view.with_external_nullifier(registry_id::bytes_to_hex(&bound))
    } else {
        view
    };
    ok_json(view)
}

pub(crate) fn get_epoch_quota_impl(
    store: Result<Arc<Store>, ApiError>,
    registry_id_raw: &str,
    rln_identifier_hex: &str,
    timestamp: &str,
) -> Result<serde_json::Value, ApiError> {
    let (registry, _, rln_id_hex) = parse_scope(registry_id_raw, rln_identifier_hex)?;
    backend_of(&registry)?;
    let (epoch_index, size, ..) = fresh_epoch_for(&registry.canonical, timestamp)?;

    let store = store?;
    let records = records_for_registry(&store, &registry);
    let usable: Vec<_> = scope_candidates(&records, &rln_id_hex)
        .into_iter()
        .filter(|r| !r.quarantined && r.cache.state.is_usable())
        .collect();
    if usable.is_empty() {
        return ok_json(views::EpochQuotaView::new(epoch_index, 0, 0));
    }
    if usable.len() > 1 {
        return Err(ApiError::new(
            ErrorKind::AmbiguousSelection,
            "multiple memberships back this scope; use select_membership",
        ));
    }
    let record = &usable[0];
    let rate_limit = record.cache.rate_limit.unwrap_or(0);

    let remaining =
        store.remaining_budget(&record.hash, &rln_id_hex, epoch_index, rate_limit, size)?;
    ok_json(views::EpochQuotaView::new(
        epoch_index,
        rate_limit,
        remaining,
    ))
}

pub(crate) fn get_registry_parameters_impl(
    registry_id_raw: &str,
    rln_identifier_hex: &str,
) -> Result<serde_json::Value, ApiError> {
    let (registry, _, _) = parse_scope(registry_id_raw, rln_identifier_hex)?;
    let backend = backend_of(&registry)?;

    let bounds = backend.registry.get_registry_bounds(&registry)?;
    let (epoch_size_sec, max_epoch_gap) = epoch_params_for(&registry.canonical)?;
    let view = views::RegistryParametersView::from_bounds(epoch_size_sec, max_epoch_gap, bounds);
    ok_json(view)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{epoch_size, reset_config_for_test};
    use crate::generated::RlnModule;
    use crate::lifecycle::MembershipState;
    use crate::sealed_store;
    use crate::start_impl;
    use crate::test_support::{imp_with_store, no_store, seed_membership, TEST_GLOBAL_LOCK};

    #[test]
    fn rate_limiting_before_start_is_not_ready() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        reset_config_for_test();
        let registry = format!("logos:local:{}", "ef".repeat(32));
        let rln_id_hex = "09".repeat(32);
        let signal_hex = "aa";

        let ts = now_unix().to_string();
        let err = get_epoch_quota_impl(no_store(), &registry, &rln_id_hex, &ts).unwrap_err();
        assert_eq!(err.kind, ErrorKind::NotReady);
        let err =
            generate_proof_impl(no_store(), &registry, &rln_id_hex, signal_hex, &ts).unwrap_err();
        assert_eq!(err.kind, ErrorKind::NotReady);
        let err = validate_proof_impl(&registry, &rln_id_hex, signal_hex, &ts, "{}").unwrap_err();
        assert_eq!(err.kind, ErrorKind::NotReady);

        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
    }

    #[test]
    fn validate_proof_impl_serves_from_local_window() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        nullifier_log::reset_for_test();
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
        let account = "ab".repeat(32);
        let registry = format!("logos:local:{account}");
        let canonical = registry.clone();
        let rln_id = [9u8; 32];
        let rln_id_hex = registry_id::bytes_to_hex(&rln_id);
        let signal = b"hot-path-signal";
        let signal_hex = registry_id::bytes_to_hex(signal);

        let epoch = rate_limit::current_epoch(now_unix(), epoch_size().unwrap());
        let ts = (epoch * 600).to_string();
        let rlp = proof::generate_for_test(&[7u8; 32], signal, epoch, &rln_id);
        let root = rlp.root();
        let proof_json = rlp.to_json().to_string();

        let cold =
            validate_proof_impl(&registry, &rln_id_hex, &signal_hex, &ts, &proof_json).unwrap_err();
        assert_eq!(cold.kind, ErrorKind::NotReady);

        roots::set_window_for_test(&canonical, vec![root], now_unix());
        let ok =
            validate_proof_impl(&registry, &rln_id_hex, &signal_hex, &ts, &proof_json).unwrap();
        assert_eq!(ok, serde_json::json!({ "verdict": "valid" }));

        let other = registry_id::bytes_to_hex(b"another-signal");
        let bad = validate_proof_impl(&registry, &rln_id_hex, &other, &ts, &proof_json).unwrap();
        assert_eq!(bad, serde_json::json!({ "verdict": "invalid" }));

        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
    }

    #[test]
    fn validate_proof_prehashed_is_interchangeable_with_raw() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        nullifier_log::reset_for_test();
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
        let registry = format!("logos:local:{}", "cd".repeat(32));
        let rln_id = [9u8; 32];
        let rln_id_hex = registry_id::bytes_to_hex(&rln_id);
        let signal = b"prehashed-signal";
        let signal_hex = registry_id::bytes_to_hex(signal);
        let hash_hex = registry_id::bytes_to_hex(&rln_signal::signal_hash(signal));

        let epoch = rate_limit::current_epoch(now_unix(), epoch_size().unwrap());
        let ts = (epoch * 600).to_string();
        let rlp = proof::generate_for_test(&[7u8; 32], signal, epoch, &rln_id);
        let proof_json = rlp.to_json().to_string();
        assert_eq!(rlp.to_json()["share_x"].as_str().unwrap(), hash_hex);
        roots::set_window_for_test(&registry, vec![rlp.root()], now_unix());

        let prehashed = |hex: &str| {
            validate_proof_with(
                &registry,
                &rln_id_hex,
                SignalArg::Prehashed(hex),
                &ts,
                &proof_json,
            )
        };
        assert_eq!(
            prehashed(&hash_hex).unwrap(),
            serde_json::json!({ "verdict": "valid" })
        );
        let dup =
            validate_proof_impl(&registry, &rln_id_hex, &signal_hex, &ts, &proof_json).unwrap();
        assert_eq!(dup, serde_json::json!({ "verdict": "duplicate" }));
        let other = registry_id::bytes_to_hex(&rln_signal::signal_hash(b"another"));
        assert_eq!(
            prehashed(&other).unwrap(),
            serde_json::json!({ "verdict": "invalid" })
        );
        for bad in ["ff".repeat(32), "ab".repeat(31), signal_hex, "zz".into()] {
            let err = prehashed(&bad).unwrap_err();
            assert_eq!(
                err.kind,
                ErrorKind::InvalidArgument,
                "{bad}: {}",
                err.message
            );
        }

        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
    }

    #[test]
    fn root_window_miss_answers_invalid_and_nudges_the_refresher() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
        let registry = format!("logos:local:{}", "bc".repeat(32));
        let rln_id = [9u8; 32];
        let rln_id_hex = registry_id::bytes_to_hex(&rln_id);
        let signal = b"root-miss-check";
        let signal_hex = registry_id::bytes_to_hex(signal);
        let epoch = rate_limit::current_epoch(now_unix(), epoch_size().unwrap());
        let rlp = proof::generate_for_test(&[7u8; 32], signal, epoch, &rln_id);

        roots::set_window_for_test(&registry, vec![[3u8; 32]], now_unix());
        roots::reset_nudge_for_test();
        let before = crate::worker::nudges_for_test();
        let out = validate_proof_impl(
            &registry,
            &rln_id_hex,
            &signal_hex,
            &(epoch * 600).to_string(),
            &rlp.to_json().to_string(),
        )
        .unwrap();
        assert_eq!(out, serde_json::json!({ "verdict": "invalid" }));
        assert_eq!(
            crate::worker::nudges_for_test(),
            before + 1,
            "a root miss must nudge"
        );

        roots::set_window_for_test(&registry, vec![rlp.root()], now_unix());
        roots::reset_nudge_for_test();
        let before = crate::worker::nudges_for_test();
        let other = registry_id::bytes_to_hex(b"a-different-signal");
        let out = validate_proof_impl(
            &registry,
            &rln_id_hex,
            &other,
            &(epoch * 600).to_string(),
            &rlp.to_json().to_string(),
        )
        .unwrap();
        assert_eq!(out, serde_json::json!({ "verdict": "invalid" }));
        assert_eq!(
            crate::worker::nudges_for_test(),
            before,
            "a crypto-invalid proof must not nudge"
        );
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
    }

    #[test]
    fn validate_proof_impl_rejects_stale_epoch_and_foreign_application() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
        let registry = format!("logos:local:{}", "ba".repeat(32));
        let rln_id = [9u8; 32];
        let rln_id_hex = registry_id::bytes_to_hex(&rln_id);
        let signal = b"binding-check";
        let signal_hex = registry_id::bytes_to_hex(signal);

        let stale = proof::generate_for_test(&[7u8; 32], signal, 1, &rln_id);
        let stale_ts = (600u64).to_string();
        roots::set_window_for_test(&registry, vec![stale.root()], now_unix());
        let out = validate_proof_impl(
            &registry,
            &rln_id_hex,
            &signal_hex,
            &stale_ts,
            &stale.to_json().to_string(),
        )
        .unwrap();
        assert_eq!(out, serde_json::json!({ "verdict": "invalid" }));

        let epoch = rate_limit::current_epoch(now_unix(), epoch_size().unwrap());
        let foreign = proof::generate_for_test(&[7u8; 32], signal, epoch, &[8u8; 32]);
        roots::set_window_for_test(&registry, vec![foreign.root()], now_unix());
        let out = validate_proof_impl(
            &registry,
            &rln_id_hex,
            &signal_hex,
            &(epoch * 600).to_string(),
            &foreign.to_json().to_string(),
        )
        .unwrap();
        assert_eq!(out, serde_json::json!({ "verdict": "invalid" }));

        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
    }

    #[test]
    fn validate_proof_impl_rejects_tampered_carried_epoch() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
        let registry = format!("logos:local:{}", "ca".repeat(32));
        let rln_id = [9u8; 32];
        let rln_id_hex = registry_id::bytes_to_hex(&rln_id);
        let signal = b"tampered-epoch";
        let signal_hex = registry_id::bytes_to_hex(signal);

        let rlp = proof::generate_for_test(&[7u8; 32], signal, 1, &rln_id);
        roots::set_window_for_test(&registry, vec![rlp.root()], now_unix());

        let now_epoch = rate_limit::current_epoch(now_unix(), epoch_size().unwrap());
        let mut epoch_bytes = [0u8; 32];
        epoch_bytes[..8].copy_from_slice(&now_epoch.to_le_bytes());
        let mut tampered = rlp.to_json();
        tampered["epoch"] = serde_json::json!(registry_id::bytes_to_hex(&epoch_bytes));

        let out = validate_proof_impl(
            &registry,
            &rln_id_hex,
            &signal_hex,
            &(now_epoch * 600).to_string(),
            &tampered.to_string(),
        )
        .unwrap();
        assert_eq!(out, serde_json::json!({ "verdict": "invalid" }));

        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
    }

    #[test]
    fn validate_proof_impl_respects_configured_epoch_gap() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        nullifier_log::reset_for_test();
        let out = start_impl(r#"{"epoch_size_sec": 600, "max_epoch_gap": 2}"#).unwrap();
        assert_eq!(out["max_epoch_gap"], serde_json::json!(2));
        let registry = format!("logos:local:{}", "da".repeat(32));
        let rln_id = [9u8; 32];
        let rln_id_hex = registry_id::bytes_to_hex(&rln_id);
        let signal = b"gap-check";
        let signal_hex = registry_id::bytes_to_hex(signal);
        let now_epoch = rate_limit::current_epoch(now_unix(), epoch_size().unwrap());

        let within = proof::generate_for_test(&[7u8; 32], signal, now_epoch - 2, &rln_id);
        roots::set_window_for_test(&registry, vec![within.root()], now_unix());
        let ok = validate_proof_impl(
            &registry,
            &rln_id_hex,
            &signal_hex,
            &((now_epoch - 2) * 600).to_string(),
            &within.to_json().to_string(),
        )
        .unwrap();
        assert_eq!(ok, serde_json::json!({ "verdict": "valid" }));

        let beyond = proof::generate_for_test(&[7u8; 32], signal, now_epoch - 3, &rln_id);
        roots::set_window_for_test(&registry, vec![beyond.root()], now_unix());
        let out = validate_proof_impl(
            &registry,
            &rln_id_hex,
            &signal_hex,
            &((now_epoch - 3) * 600).to_string(),
            &beyond.to_json().to_string(),
        )
        .unwrap();
        assert_eq!(out, serde_json::json!({ "verdict": "invalid" }));

        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
    }

    #[test]
    fn validate_proof_impl_requires_proof_epoch_to_match_timestamp() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        nullifier_log::reset_for_test();
        start_impl(r#"{"epoch_size_sec": 600, "max_epoch_gap": 2}"#).unwrap();
        let registry = format!("logos:local:{}", "db".repeat(32));
        let rln_id = [9u8; 32];
        let rln_id_hex = registry_id::bytes_to_hex(&rln_id);
        let signal = b"epoch-equality";
        let signal_hex = registry_id::bytes_to_hex(signal);
        let now_epoch = rate_limit::current_epoch(now_unix(), epoch_size().unwrap());

        let rlp = proof::generate_for_test(&[7u8; 32], signal, now_epoch, &rln_id);
        roots::set_window_for_test(&registry, vec![rlp.root()], now_unix());
        let proof_json = rlp.to_json().to_string();

        let earlier = ((now_epoch - 1) * 600).to_string();
        let out = validate_proof_impl(&registry, &rln_id_hex, &signal_hex, &earlier, &proof_json)
            .unwrap();
        assert_eq!(out, serde_json::json!({ "verdict": "invalid" }));

        let honest = (now_epoch * 600).to_string();
        let ok =
            validate_proof_impl(&registry, &rln_id_hex, &signal_hex, &honest, &proof_json).unwrap();
        assert_eq!(ok, serde_json::json!({ "verdict": "valid" }));

        let bound = proof::generate_for_test(&[7u8; 32], signal, now_epoch - 1, &rln_id);
        roots::set_window_for_test(&registry, vec![bound.root()], now_unix());
        let mut rewritten = bound.to_json();
        rewritten["epoch"] = serde_json::json!(now_epoch);
        let out = validate_proof_impl(
            &registry,
            &rln_id_hex,
            &signal_hex,
            &((now_epoch - 1) * 600).to_string(),
            &rewritten.to_string(),
        )
        .unwrap();
        assert_eq!(out, serde_json::json!({ "verdict": "invalid" }));

        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
    }

    #[test]
    fn validate_proof_impl_reconstructs_mix_external_nullifier() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        nullifier_log::reset_for_test();
        start_impl(r#"{"epoch_size_sec": 10, "max_epoch_gap": 3}"#).unwrap();
        let registry = format!("logos:local:{}", "dc".repeat(32));
        let id = [9u8; 32];
        let scope = registry_id::bytes_to_hex(&id);
        let signal = b"mix packet";
        let signal_hex = registry_id::bytes_to_hex(signal);
        let timestamp = now_unix();
        let epoch = timestamp / 10;
        let proof = proof::generate_for_test(&[7u8; 32], signal, epoch, &id);
        roots::set_window_for_test(&registry, vec![proof.root()], timestamp);
        let mut wire = proof.to_json();
        wire.as_object_mut().unwrap().remove("external_nullifier");
        let wire = wire.to_string();
        let time = timestamp.to_string();
        let wrong =
            validate_proof_impl(&registry, &"aa".repeat(32), &signal_hex, &time, &wire).unwrap();
        assert_eq!(wrong["verdict"], "invalid");
        assert!(wrong.get("external_nullifier").is_none());
        let wrong = validate_proof_impl(&registry, &scope, "00", &time, &wire).unwrap();
        assert_eq!(wrong["verdict"], "invalid");
        assert!(wrong.get("external_nullifier").is_none());
        let valid = validate_proof_impl(&registry, &scope, &signal_hex, &time, &wire).unwrap();
        assert_eq!(valid["verdict"], "valid");
        assert_eq!(
            valid["external_nullifier"],
            registry_id::bytes_to_hex(&proof.external_nullifier())
        );
        let duplicate = validate_proof_impl(&registry, &scope, &signal_hex, &time, &wire).unwrap();
        assert_eq!(duplicate["verdict"], "duplicate");
        assert_eq!(
            duplicate["external_nullifier"],
            registry_id::bytes_to_hex(&proof.external_nullifier())
        );
    }

    #[test]
    fn validate_proof_impl_resolves_epochless_proof_from_timestamp() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        nullifier_log::reset_for_test();
        start_impl(r#"{"epoch_size_sec": 600, "max_epoch_gap": 2}"#).unwrap();
        let registry = format!("logos:local:{}", "dc".repeat(32));
        let rln_id = [9u8; 32];
        let rln_id_hex = registry_id::bytes_to_hex(&rln_id);
        let signal = b"epochless";
        let signal_hex = registry_id::bytes_to_hex(signal);
        let now_epoch = rate_limit::current_epoch(now_unix(), epoch_size().unwrap());

        let rlp = proof::generate_for_test(&[7u8; 32], signal, now_epoch - 1, &rln_id);
        roots::set_window_for_test(&registry, vec![rlp.root()], now_unix());
        let mut json = rlp.to_json();
        json.as_object_mut().unwrap().remove("epoch");
        let proof_json = json.to_string();

        let neighbor = (now_epoch * 600).to_string();
        let out = validate_proof_impl(&registry, &rln_id_hex, &signal_hex, &neighbor, &proof_json)
            .unwrap();
        assert_eq!(out, serde_json::json!({ "verdict": "invalid" }));

        let honest = ((now_epoch - 1) * 600).to_string();
        let ok =
            validate_proof_impl(&registry, &rln_id_hex, &signal_hex, &honest, &proof_json).unwrap();
        assert_eq!(ok, serde_json::json!({ "verdict": "valid" }));

        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
    }

    #[test]
    fn validate_proof_rate_limit_violation_recovers_secret() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        nullifier_log::reset_for_test();
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
        let registry = format!("logos:local:{}", "e1".repeat(32));
        let rln_id = [9u8; 32];
        let rln_id_hex = registry_id::bytes_to_hex(&rln_id);
        let epoch = rate_limit::current_epoch(now_unix(), epoch_size().unwrap());

        let pa = proof::generate_for_test(&[7u8; 32], b"sig-A", epoch, &rln_id);
        let pb = proof::generate_for_test(&[7u8; 32], b"sig-B", epoch, &rln_id);
        roots::set_window_for_test(&registry, vec![pa.root()], now_unix());

        let ts = (epoch * 600).to_string();
        let sig_a = registry_id::bytes_to_hex(b"sig-A");
        let first = validate_proof_impl(
            &registry,
            &rln_id_hex,
            &sig_a,
            &ts,
            &pa.to_json().to_string(),
        )
        .unwrap();
        assert_eq!(first, serde_json::json!({ "verdict": "valid" }));

        let sig_b = registry_id::bytes_to_hex(b"sig-B");
        let second = validate_proof_impl(
            &registry,
            &rln_id_hex,
            &sig_b,
            &ts,
            &pb.to_json().to_string(),
        )
        .unwrap();
        assert_eq!(second["verdict"], serde_json::json!("rate_limit_violation"));
        assert_eq!(
            second["recovered_secret"],
            serde_json::json!("3c87aa7480ec2cad022ef39c256ddb6e4fb083c7d4a0dfdc4eee891feda7a62b")
        );

        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
    }

    #[test]
    fn validate_proof_duplicate_on_retransmission() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        nullifier_log::reset_for_test();
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
        let registry = format!("logos:local:{}", "e2".repeat(32));
        let rln_id = [9u8; 32];
        let rln_id_hex = registry_id::bytes_to_hex(&rln_id);
        let epoch = rate_limit::current_epoch(now_unix(), epoch_size().unwrap());

        let p = proof::generate_for_test(&[7u8; 32], b"dup-sig", epoch, &rln_id);
        roots::set_window_for_test(&registry, vec![p.root()], now_unix());
        let ts = (epoch * 600).to_string();
        let sig = registry_id::bytes_to_hex(b"dup-sig");
        let proof_json = p.to_json().to_string();

        let first = validate_proof_impl(&registry, &rln_id_hex, &sig, &ts, &proof_json).unwrap();
        assert_eq!(first, serde_json::json!({ "verdict": "valid" }));

        let second = validate_proof_impl(&registry, &rln_id_hex, &sig, &ts, &proof_json).unwrap();
        assert_eq!(second["verdict"], serde_json::json!("duplicate"));
        assert!(second.get("recovered_secret").is_none());

        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
    }

    #[test]
    fn validate_proof_invalid_never_logs() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        nullifier_log::reset_for_test();
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
        let registry = format!("logos:local:{}", "e3".repeat(32));
        let rln_id = [9u8; 32];
        let rln_id_hex = registry_id::bytes_to_hex(&rln_id);
        let epoch = rate_limit::current_epoch(now_unix(), epoch_size().unwrap());

        let p = proof::generate_for_test(&[7u8; 32], b"correct-sig", epoch, &rln_id);
        roots::set_window_for_test(&registry, vec![p.root()], now_unix());
        let ts = (epoch * 600).to_string();
        let proof_json = p.to_json().to_string();

        let wrong = registry_id::bytes_to_hex(b"wrong-sig");
        for _ in 0..2 {
            let out =
                validate_proof_impl(&registry, &rln_id_hex, &wrong, &ts, &proof_json).unwrap();
            assert_eq!(out, serde_json::json!({ "verdict": "invalid" }));
        }

        let correct = registry_id::bytes_to_hex(b"correct-sig");
        let ok = validate_proof_impl(&registry, &rln_id_hex, &correct, &ts, &proof_json).unwrap();
        assert_eq!(ok, serde_json::json!({ "verdict": "valid" }));

        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
    }

    #[test]
    fn epoch_quota_snapshot_tracks_spent_slots() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
        let dir = std::env::temp_dir().join(format!("rln-ms-quota-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let store = Store::open(dir.clone()).expect("test store open");

        let registry = format!("logos:local:{}", "aa".repeat(32));
        let rln_id = "ef".repeat(32);

        let now = now_unix();
        let ts = now.to_string();

        let q = get_epoch_quota_impl(Ok(Arc::clone(&store)), &registry, &rln_id, &ts).unwrap();
        assert_eq!(q["rate_limit"], 0, "got: {q}");
        assert_eq!(q["remaining"], 0, "got: {q}");
        assert!(q["epoch_index"].as_u64().is_some(), "got: {q}");

        let commitment = [0x77u8; 32];
        let hash = registry_id::membership_hash(&registry, &commitment);
        store.unlock("pw").unwrap();
        seed_membership(
            &store,
            &hash,
            &registry,
            &registry_id::bytes_to_hex(&commitment),
            &rln_id,
            &"88".repeat(32),
            MembershipState::Active,
            4,
            100,
        );

        let fresh = get_epoch_quota_impl(Ok(Arc::clone(&store)), &registry, &rln_id, &ts).unwrap();
        assert_eq!(fresh["rate_limit"], serde_json::json!(100));
        assert_eq!(fresh["remaining"], serde_json::json!(100));
        let epoch_index = fresh["epoch_index"].as_u64().expect("numeric epoch index");
        assert_eq!(epoch_index, now / 600);

        store
            .reserve_message_id(&hash, &rln_id, epoch_index, epoch_index, 100, 600)
            .unwrap();
        store
            .reserve_message_id(&hash, &rln_id, epoch_index, epoch_index, 100, 600)
            .unwrap();
        let spent = get_epoch_quota_impl(Ok(Arc::clone(&store)), &registry, &rln_id, &ts).unwrap();
        assert_eq!(spent["epoch_index"], serde_json::json!(epoch_index));
        assert_eq!(spent["remaining"], serde_json::json!(98));

        let next_ts = ((epoch_index + 1) * 600).to_string();
        let next =
            get_epoch_quota_impl(Ok(Arc::clone(&store)), &registry, &rln_id, &next_ts).unwrap();
        assert_eq!(next["epoch_index"], serde_json::json!(epoch_index + 1));
        assert_eq!(next["rate_limit"], serde_json::json!(100));
        assert_eq!(next["remaining"], serde_json::json!(100));

        store.close();
        let _ = std::fs::remove_dir_all(&dir);
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
    }

    #[test]
    fn epoch_quota_rejects_bad_or_out_of_window_timestamp() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
        let registry = format!("logos:local:{}", "ae".repeat(32));
        let rln_id = "ef".repeat(32);

        let err = get_epoch_quota_impl(no_store(), &registry, &rln_id, "not-a-number").unwrap_err();
        assert_eq!(err.kind, ErrorKind::InvalidArgument);

        let err = get_epoch_quota_impl(no_store(), &registry, &rln_id, "0").unwrap_err();
        assert_eq!(err.kind, ErrorKind::InvalidArgument);
        assert_eq!(err.kind.class(), "permanent");
        assert!(err.message.contains("epoch window"), "got: {}", err.message);
    }

    #[test]
    fn validate_proof_impl_rejects_malformed_input() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
        let registry = format!("logos:local:{}", "cd".repeat(32));
        let rln_id_hex = "ef".repeat(32);
        let ts = now_unix().to_string();
        let e1 = validate_proof_impl(&registry, &rln_id_hex, "zz", &ts, "{}").unwrap_err();
        assert_eq!(e1.kind, ErrorKind::InvalidArgument);
        let e2 = validate_proof_impl(&registry, &rln_id_hex, "00", &ts, "not json").unwrap_err();
        assert_eq!(e2.kind, ErrorKind::InvalidArgument);
        let e3 = validate_proof_impl(&registry, &rln_id_hex, "00", "later", "{}").unwrap_err();
        assert_eq!(e3.kind, ErrorKind::InvalidArgument);
        assert!(e3.message.contains("timestamp"), "got: {}", e3.message);
        let e4 = get_epoch_quota_impl(no_store(), &registry, &rln_id_hex, "later").unwrap_err();
        assert_eq!(e4.kind, ErrorKind::InvalidArgument);
        assert!(e4.message.contains("timestamp"), "got: {}", e4.message);
    }

    #[test]
    fn generate_proof_impl_rejects_bad_signal_before_touching_state() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
        let registry = format!("logos:local:{}", "cd".repeat(32));
        let rln_id_hex = "ef".repeat(32);
        let err = generate_proof_impl(
            no_store(),
            &registry,
            &rln_id_hex,
            "nothex",
            &now_unix().to_string(),
        )
        .unwrap_err();
        assert_eq!(err.kind, ErrorKind::InvalidArgument);
    }

    #[test]
    fn generate_proof_impl_refuses_a_usable_row_without_a_leaf_index() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        let dir = std::env::temp_dir().join(format!("rln-ms-no-leaf-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let (imp, store) = imp_with_store(dir.clone());
        assert!(imp
            .unlock_keystore("pw".into())
            .contains(r#""unlocked":true"#));

        let reg = format!("logos:local:{}", "ab".repeat(32));
        let rln_id_hex = "ef".repeat(32);
        let (commitment_hex, secret_hex) = proof::generate_identity().expect("test identity");
        let commitment =
            registry_id::hex_to_bytes32(&commitment_hex).expect("generated commitment is 32 bytes");
        let hash = registry_id::membership_hash(&reg, &commitment);

        seed_membership(
            &store,
            &hash,
            &reg,
            &commitment_hex,
            &rln_id_hex,
            &secret_hex,
            MembershipState::Active,
            5,
            300,
        );
        path_cache::set_path_for_test(
            &hash,
            vec!["00".repeat(32); proof::RLN_TREE_DEPTH],
            vec![0u8; proof::RLN_TREE_DEPTH],
            0,
        );
        store
            .update_cache(&hash, |m| m.leaf_index = None)
            .expect("clear the leaf");

        let err = generate_proof_impl(Ok(store), &reg, &rln_id_hex, "aa", &now_unix().to_string())
            .expect_err("a usable row without a leaf must not prove against leaf 0");
        assert_eq!(
            err.kind,
            ErrorKind::UnknownMembership,
            "got: {}",
            err.message
        );
        assert!(err.message.contains("leaf_index"), "got: {}", err.message);

        sealed_store::store::publish(None);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn generate_proof_impl_serves_cached_path_with_zero_registry_io() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        let dir =
            std::env::temp_dir().join(format!("rln-ms-path-cache-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let (imp, store) = imp_with_store(dir.clone());
        assert!(imp
            .unlock_keystore("pw".into())
            .contains(r#""unlocked":true"#));

        let reg = format!("logos:local:{}", "ab".repeat(32));
        let rln_id_hex = "ef".repeat(32);
        let (commitment_hex, secret_hex) = proof::generate_identity().expect("test identity");
        let commitment =
            registry_id::hex_to_bytes32(&commitment_hex).expect("generated commitment is 32 bytes");
        let hash = registry_id::membership_hash(&reg, &commitment);
        let leaf_index = 5u64;

        seed_membership(
            &store,
            &hash,
            &reg,
            &commitment_hex,
            &rln_id_hex,
            &secret_hex,
            MembershipState::Active,
            leaf_index,
            300,
        );

        let signal_hex = "aa";

        let miss = generate_proof_impl(
            Ok(Arc::clone(&store)),
            &reg,
            &rln_id_hex,
            signal_hex,
            &now_unix().to_string(),
        )
        .unwrap_err();
        assert_eq!(
            miss.kind,
            ErrorKind::ProviderFailure,
            "a cold cache must fall back to the registry: {}",
            miss.message
        );

        path_cache::set_path_for_test(
            &hash,
            vec!["00".repeat(32); proof::RLN_TREE_DEPTH],
            vec![0u8; proof::RLN_TREE_DEPTH],
            leaf_index,
        );
        let out = generate_proof_impl(
            Ok(store),
            &reg,
            &rln_id_hex,
            signal_hex,
            &now_unix().to_string(),
        )
        .expect("a warm cache entry needs no registry call");
        assert!(
            out.get("proof").and_then(|v| v.as_str()).is_some(),
            "got: {out}"
        );
        assert!(
            out.get("root").and_then(|v| v.as_str()).is_some(),
            "got: {out}"
        );
        assert_eq!(
            out.get("message_id").and_then(|v| v.as_u64()),
            Some(0),
            "first allocation on a fresh (rln_identifier, epoch): {out}"
        );
        assert_eq!(
            out.get("membership_hash").and_then(|v| v.as_str()),
            Some(hash.as_str())
        );

        sealed_store::store::publish(None);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn generate_proof_prehashed_mints_a_proof_both_dialects_validate() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        nullifier_log::reset_for_test();
        let dir =
            std::env::temp_dir().join(format!("rln-ms-prehashed-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
        let (imp, store) = imp_with_store(dir.clone());
        assert!(imp
            .unlock_keystore("pw".into())
            .contains(r#""unlocked":true"#));

        let reg = format!("logos:local:{}", "ac".repeat(32));
        let rln_id_hex = "ee".repeat(32);
        let (commitment_hex, secret_hex) = proof::generate_identity().expect("test identity");
        let commitment =
            registry_id::hex_to_bytes32(&commitment_hex).expect("generated commitment is 32 bytes");
        let hash = registry_id::membership_hash(&reg, &commitment);
        let leaf_index = 5u64;
        seed_membership(
            &store,
            &hash,
            &reg,
            &commitment_hex,
            &rln_id_hex,
            &secret_hex,
            MembershipState::Active,
            leaf_index,
            300,
        );
        path_cache::set_path_for_test(
            &hash,
            vec!["00".repeat(32); proof::RLN_TREE_DEPTH],
            vec![0u8; proof::RLN_TREE_DEPTH],
            leaf_index,
        );

        let signal = b"payload bytes, then a content topic, then eight timestamp bytes";
        let signal_hex = registry_id::bytes_to_hex(signal);
        let hash_hex = registry_id::bytes_to_hex(&rln_signal::signal_hash(signal));
        let ts = now_unix().to_string();

        let bad = generate_proof_with(
            Ok(Arc::clone(&store)),
            &reg,
            &rln_id_hex,
            SignalArg::Prehashed(&"ff".repeat(32)),
            &ts,
        )
        .unwrap_err();
        assert_eq!(bad.kind, ErrorKind::InvalidArgument, "got: {}", bad.message);

        let out = generate_proof_with(
            Ok(store),
            &reg,
            &rln_id_hex,
            SignalArg::Prehashed(&hash_hex),
            &ts,
        )
        .expect("prehashed generate over a warm cache");
        assert_eq!(out["share_x"].as_str().unwrap(), hash_hex, "got: {out}");
        assert_eq!(
            out["message_id"].as_u64(),
            Some(0),
            "the refused hash must not have spent a slot: {out}"
        );
        let root = registry_id::hex_to_bytes32(out["root"].as_str().unwrap()).expect("root");
        roots::set_window_for_test(&reg, vec![root], now_unix());
        let proof_json = out.to_string();

        let raw = validate_proof_impl(&reg, &rln_id_hex, &signal_hex, &ts, &proof_json).unwrap();
        assert_eq!(raw, serde_json::json!({ "verdict": "valid" }));
        let pre = validate_proof_with(
            &reg,
            &rln_id_hex,
            SignalArg::Prehashed(&hash_hex),
            &ts,
            &proof_json,
        )
        .unwrap();
        assert_eq!(pre, serde_json::json!({ "verdict": "duplicate" }));

        sealed_store::store::publish(None);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn generate_proof_impl_derives_epoch_from_supplied_timestamp() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        let dir =
            std::env::temp_dir().join(format!("rln-ms-epoch-src-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        start_impl(r#"{"epoch_size_sec": 600, "max_epoch_gap": 1}"#).unwrap();

        let (imp, store) = imp_with_store(dir.clone());
        assert!(imp
            .unlock_keystore("pw".into())
            .contains(r#""unlocked":true"#));

        let reg = format!("logos:local:{}", "1a".repeat(32));
        let rln_id_hex = "2b".repeat(32);
        let (commitment_hex, secret_hex) = proof::generate_identity().expect("test identity");
        let commitment = registry_id::hex_to_bytes32(&commitment_hex).unwrap();
        let hash = registry_id::membership_hash(&reg, &commitment);
        let leaf_index = 3u64;
        seed_membership(
            &store,
            &hash,
            &reg,
            &commitment_hex,
            &rln_id_hex,
            &secret_hex,
            MembershipState::Active,
            leaf_index,
            300,
        );
        path_cache::set_path_for_test(
            &hash,
            vec!["00".repeat(32); proof::RLN_TREE_DEPTH],
            vec![0u8; proof::RLN_TREE_DEPTH],
            leaf_index,
        );

        let size = epoch_size().unwrap();
        let now_epoch = rate_limit::current_epoch(now_unix(), size);
        let ts = (now_unix() - size).to_string();
        let out = generate_proof_impl(Ok(store), &reg, &rln_id_hex, "aa", &ts)
            .expect("a past-but-in-window timestamp still proves");
        assert_eq!(
            out.get("epoch_index").and_then(|v| v.as_u64()),
            Some(now_epoch - 1),
            "epoch must derive from the supplied timestamp, not the module clock: {out}"
        );
        let canonical = out
            .get("proof_canonical")
            .and_then(|v| v.as_str())
            .expect("reply carries proof_canonical");
        assert_eq!(canonical.len(), 289 * 2);
        assert!(canonical.starts_with(out["proof"].as_str().unwrap()));

        sealed_store::store::publish(None);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn generate_proof_impl_rejects_timestamp_outside_epoch_window() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        reset_config_for_test();
        start_impl(r#"{"epoch_size_sec": 600, "max_epoch_gap": 1}"#).unwrap();
        let registry = format!("logos:local:{}", "3c".repeat(32));
        let rln_id_hex = "4d".repeat(32);
        let stale = (now_unix() - 100 * 600).to_string();
        let err =
            generate_proof_impl(no_store(), &registry, &rln_id_hex, "aa", &stale).unwrap_err();
        assert_eq!(err.kind, ErrorKind::InvalidArgument);
        assert!(err.message.contains("window"), "got: {}", err.message);
    }

    fn le_root(byte: u8) -> [u8; 32] {
        let mut root = [0u8; 32];
        root[0] = byte;
        root
    }

    fn depth10_elements(sibling0: &str) -> Vec<String> {
        let mut elements = vec!["00".repeat(32); proof::RLN_TREE_DEPTH];
        elements[0] = sibling0.to_string();
        elements
    }

    fn depth10_proof(root: [u8; 32], sibling0: &str, valid: &[[u8; 32]]) -> serde_json::Value {
        serde_json::json!({
            "depth": proof::RLN_TREE_DEPTH,
            "leaf": "00".repeat(32),
            "leaf_index": 5,
            "path_elements": depth10_elements(sibling0),
            "path_indices": vec![0u64; proof::RLN_TREE_DEPTH],
            "root": registry_id::bytes_to_hex(&root),
            "valid_roots": valid
                .iter()
                .map(|r| registry_id::bytes_to_hex(r))
                .collect::<Vec<_>>(),
        })
    }

    struct OpenMembership {
        dir: std::path::PathBuf,
        store: Arc<Store>,
        hash: String,
        rln_id_hex: String,
        _imp: crate::test_support::TestImp,
    }

    fn open_membership(tag: &str, registry: &str) -> OpenMembership {
        let dir = std::env::temp_dir().join(format!("rln-root-{tag}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let (imp, store) = imp_with_store(dir.clone());
        assert!(imp
            .unlock_keystore("pw".into())
            .contains(r#""unlocked":true"#));
        let rln_id_hex = "ef".repeat(32);
        let (commitment_hex, secret_hex) = proof::generate_identity().expect("test identity");
        let commitment = registry_id::hex_to_bytes32(&commitment_hex).expect("commitment");
        let hash = registry_id::membership_hash(registry, &commitment);
        seed_membership(
            &store,
            &hash,
            registry,
            &commitment_hex,
            &rln_id_hex,
            &secret_hex,
            MembershipState::Active,
            5,
            100,
        );
        OpenMembership {
            dir,
            store,
            hash,
            rln_id_hex,
            _imp: imp,
        }
    }

    fn install_proof_tree(proof: Option<serde_json::Value>) {
        use crate::provider::fake::{self, FakePayer, FakeRegistry, FakeTree};
        crate::test_support::install_backend(fake::backend(
            FakeTree { proof, roots: None },
            FakeRegistry::default(),
            FakePayer::default(),
        ));
    }

    fn budget_left(store: &Store, hash: &str, rln_id_hex: &str) -> u64 {
        let size = epoch_size().unwrap();
        let epoch = rate_limit::current_epoch(now_unix(), size);
        store
            .remaining_budget(hash, rln_id_hex, epoch, 100, size)
            .expect("budget")
    }

    fn close_membership(opened: &OpenMembership) {
        sealed_store::store::publish(None);
        let _ = std::fs::remove_dir_all(&opened.dir);
    }

    #[test]
    fn generate_proof_accepts_a_cached_root_inside_the_window() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
        let registry = "fakens:local:root-in";
        let opened = open_membership("in", registry);
        let new_root = le_root(2);
        path_cache::set_rooted_path_for_test(
            &opened.hash,
            depth10_elements(&"00".repeat(32)),
            vec![0u8; proof::RLN_TREE_DEPTH],
            5,
            new_root,
        );
        let version = path_cache::hit(&opened.hash, 5).unwrap().version;
        roots::set_window_for_test(registry, vec![new_root], now_unix());
        install_proof_tree(None);

        let out = generate_proof_impl(
            Ok(Arc::clone(&opened.store)),
            registry,
            &opened.rln_id_hex,
            "aa",
            &now_unix().to_string(),
        )
        .expect("a root inside the window proves without a refill");
        assert!(
            out.get("proof").and_then(|v| v.as_str()).is_some(),
            "got: {out}"
        );
        assert_eq!(out["message_id"].as_u64(), Some(0), "got: {out}");
        assert_eq!(
            path_cache::hit(&opened.hash, 5).unwrap().version,
            version,
            "an accepted root must not refill"
        );
        assert_eq!(
            budget_left(&opened.store, &opened.hash, &opened.rln_id_hex),
            99
        );

        close_membership(&opened);
    }

    #[test]
    fn generate_proof_refreshes_a_cached_root_that_left_the_window() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
        let registry = "fakens:local:root-stale";
        let opened = open_membership("stale", registry);
        let old_root = le_root(1);
        let new_root = le_root(2);
        path_cache::set_rooted_path_for_test(
            &opened.hash,
            depth10_elements(&format!("04{}", "00".repeat(31))),
            vec![0u8; proof::RLN_TREE_DEPTH],
            5,
            old_root,
        );
        let before = path_cache::hit(&opened.hash, 5).unwrap();
        roots::set_window_for_test(registry, vec![new_root], now_unix());
        let sibling = format!("03{}", "00".repeat(31));
        install_proof_tree(Some(depth10_proof(new_root, &sibling, &[new_root])));

        let out = generate_proof_impl(
            Ok(Arc::clone(&opened.store)),
            registry,
            &opened.rln_id_hex,
            "aa",
            &now_unix().to_string(),
        )
        .expect("a refreshed root inside the window proves");
        assert!(
            out.get("proof").and_then(|v| v.as_str()).is_some(),
            "got: {out}"
        );
        let after = path_cache::hit(&opened.hash, 5).expect("refreshed path");
        assert_eq!(after.root, Some(new_root));
        assert_ne!(after.path_elements_hex, before.path_elements_hex);
        assert!(after.version > before.version);
        assert_eq!(
            budget_left(&opened.store, &opened.hash, &opened.rln_id_hex),
            99
        );

        close_membership(&opened);
    }

    #[test]
    fn generate_proof_refuses_a_root_that_stays_outside_the_window() {
        let _serial = crate::lock(&TEST_GLOBAL_LOCK);
        start_impl(r#"{"epoch_size_sec": 600}"#).unwrap();
        let registry = "fakens:local:root-stuck";
        let opened = open_membership("stuck", registry);
        let stale = le_root(3);
        let old_root = le_root(1);
        let new_root = le_root(2);
        path_cache::set_rooted_path_for_test(
            &opened.hash,
            depth10_elements(&"00".repeat(32)),
            vec![0u8; proof::RLN_TREE_DEPTH],
            5,
            stale,
        );
        let before = path_cache::hit(&opened.hash, 5).unwrap().version;
        roots::set_window_for_test(registry, vec![new_root], now_unix());
        // The proof's valid_roots omit its own root, so the refill adopts a
        // window the new path is still outside.
        install_proof_tree(Some(depth10_proof(old_root, &"00".repeat(32), &[new_root])));
        assert_eq!(
            budget_left(&opened.store, &opened.hash, &opened.rln_id_hex),
            100
        );

        let err = generate_proof_impl(
            Ok(Arc::clone(&opened.store)),
            registry,
            &opened.rln_id_hex,
            "aa",
            &now_unix().to_string(),
        )
        .expect_err("a root that stays outside the window must not prove");
        assert_eq!(err.kind, ErrorKind::NotReady, "got: {}", err.message);
        assert_eq!(err.kind.class(), "not_ready");
        assert!(
            err.message.contains("accepted-root window"),
            "got: {}",
            err.message
        );
        let after = path_cache::hit(&opened.hash, 5).expect("refill still publishes");
        assert_eq!(after.root, Some(old_root));
        assert!(
            after.version > before,
            "the refusal happens after one refresh"
        );
        assert_eq!(
            budget_left(&opened.store, &opened.hash, &opened.rln_id_hex),
            100,
            "no message id is reserved"
        );

        close_membership(&opened);
    }
}
