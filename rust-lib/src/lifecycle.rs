use std::collections::BTreeMap;
use std::sync::Mutex;

use serde::{Deserialize, Serialize};
use zeroize::{Zeroize, ZeroizeOnDrop};

#[derive(Serialize, Deserialize, Clone, Copy, PartialEq, Eq, Debug)]
#[serde(rename_all = "snake_case")]
pub(crate) enum MembershipState {
    Unknown,
    Pending,
    Failed,
    Active,
    GracePeriod,
    Expired,
    ErasedAwaitsWithdrawal,
    Erased,
    Slashed,
}

impl MembershipState {
    pub(crate) fn is_usable(self) -> bool {
        matches!(self, Self::Active | Self::GracePeriod)
    }

    pub(crate) fn is_live(self) -> bool {
        matches!(self, Self::Pending) || self.is_usable()
    }

    pub(crate) fn is_active_like(self) -> bool {
        matches!(
            self,
            Self::Active
                | Self::GracePeriod
                | Self::Expired
                | Self::ErasedAwaitsWithdrawal
                | Self::Erased
                | Self::Slashed
        )
    }
}

#[derive(Serialize, Deserialize, Zeroize, ZeroizeOnDrop)]
pub(crate) struct StoredCredential {
    pub(crate) identity_commitment: String,
    pub(crate) identity_secret_hash: String,
    pub(crate) registry_id: String,
}

pub const CONFIRMATION_WINDOW_SECS: u64 = 300;

#[derive(Serialize, Deserialize, Clone, PartialEq)]
pub struct CacheState {
    pub state: MembershipState,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub leaf_index: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rate_limit: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub failed_reason: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub retryable: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tx_result: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_active_at: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub confirm_deadline: Option<u64>,
}

impl Default for CacheState {
    fn default() -> CacheState {
        CacheState {
            state: MembershipState::Unknown,
            leaf_index: None,
            rate_limit: None,
            failed_reason: None,
            retryable: None,
            tx_result: None,
            first_active_at: None,
            confirm_deadline: None,
        }
    }
}

impl CacheState {
    pub(crate) fn mark_submit_failed(&mut self, message: &str, retryable: bool) {
        self.state = MembershipState::Failed;
        self.failed_reason = Some(format!("submit_failed: {message}"));
        self.retryable = Some(retryable);
    }

    pub(crate) fn record_async_submit_error(&mut self, message: &str, retryable: bool) {
        if self.state != MembershipState::Pending || retryable {
            return;
        }
        self.mark_submit_failed(message, retryable);
    }
}

#[derive(Clone)]
pub struct MembershipRecord {
    pub hash: String,
    pub identity: crate::sealed_store::format::IdentityBlock,
    pub cache: CacheState,
    pub alloc: crate::rate_limit::AllocationState,
    pub quarantined: bool,
}

fn has_been_active(record: &MembershipRecord) -> bool {
    record.cache.first_active_at.is_some() || record.cache.state.is_active_like()
}

pub fn confirmation_deadline(record: &MembershipRecord) -> u64 {
    record.cache.confirm_deadline.unwrap_or_else(|| {
        record
            .identity
            .submitted_at
            .saturating_add(CONFIRMATION_WINDOW_SECS)
    })
}

pub fn merge_state(
    local: Option<&MembershipRecord>,
    registry_state: Option<MembershipState>,
    now: u64,
) -> MembershipState {
    match (local, registry_state) {
        (None, None) => MembershipState::Unknown,
        (_, Some(state)) => state,
        (Some(record), None) => {
            if record.cache.state == MembershipState::Pending {
                if now > confirmation_deadline(record) {
                    MembershipState::Failed
                } else {
                    MembershipState::Pending
                }
            } else if has_been_active(record) {
                MembershipState::Erased
            } else {
                record.cache.state
            }
        }
    }
}

pub fn transition_event<'a>(
    hash: &'a str,
    record: &'a MembershipRecord,
    prior: MembershipState,
    new_state: MembershipState,
) -> Option<(&'a str, &'a str, &'a str, String, String)> {
    if new_state == prior {
        return None;
    }
    let wire = |s: MembershipState| match serde_json::to_value(s) {
        Ok(serde_json::Value::String(text)) => text,
        _ => String::new(),
    };
    Some((
        &record.identity.registry_id,
        &record.identity.rln_identifier,
        hash,
        wire(new_state),
        wire(prior),
    ))
}

pub(crate) fn emit_transition(
    hash: &str,
    record: &MembershipRecord,
    prior: MembershipState,
    new_state: MembershipState,
) {
    if prior.is_usable() && !new_state.is_usable() {
        crate::proof::evict_partial(hash);
    }
    if let Some((registry_id, rln_identifier, membership_hash, state, previous)) =
        transition_event(hash, record, prior, new_state)
    {
        crate::generated::emit_membership_state_changed(
            registry_id,
            rln_identifier,
            membership_hash,
            &state,
            &previous,
        );
    }
}

pub const FORMAT_CACHE: &str = "rln-sealed-cache";

#[derive(Serialize, Deserialize, Clone)]
pub struct CacheFile {
    pub format: String,
    pub version: u32,
    pub entries: BTreeMap<String, CacheState>,
}

impl CacheFile {
    pub fn new() -> CacheFile {
        CacheFile {
            format: FORMAT_CACHE.to_string(),
            version: crate::sealed_store::format::FORMAT_VERSION,
            entries: BTreeMap::new(),
        }
    }
}

impl Default for CacheFile {
    fn default() -> CacheFile {
        CacheFile::new()
    }
}

#[derive(Serialize)]
pub struct CacheFileRef<'a> {
    pub format: &'static str,
    pub version: u32,
    pub entries: &'a BTreeMap<String, CacheState>,
}

impl<'a> CacheFileRef<'a> {
    pub fn new(entries: &'a BTreeMap<String, CacheState>) -> CacheFileRef<'a> {
        CacheFileRef {
            format: FORMAT_CACHE,
            version: crate::sealed_store::format::FORMAT_VERSION,
            entries,
        }
    }
}

static GRANTED_BY: Mutex<Option<std::collections::HashMap<String, String>>> = Mutex::new(None);

static DISCOVERY_MISSES: Mutex<Option<std::collections::HashSet<String>>> = Mutex::new(None);

pub(crate) fn note_discovery_miss(hash: &str) {
    crate::util::lock(&DISCOVERY_MISSES)
        .get_or_insert_with(std::collections::HashSet::new)
        .insert(hash.to_owned());
}

pub(crate) fn take_discovery_miss(hash: &str) -> bool {
    crate::util::lock(&DISCOVERY_MISSES)
        .as_mut()
        .is_some_and(|s| s.remove(hash))
}

pub(crate) fn note_granted_by(hash: &str, reply: &serde_json::Value) {
    let Some(peer) = reply.get("allocatorPeerId").and_then(|p| p.as_str()) else {
        return;
    };
    let discovered = reply
        .get("discovered")
        .and_then(|d| d.as_bool())
        .unwrap_or(false);
    let who = if discovered {
        format!("{peer} (discovered)")
    } else {
        peer.to_string()
    };
    crate::util::lock(&GRANTED_BY)
        .get_or_insert_with(std::collections::HashMap::new)
        .insert(hash.to_owned(), who);
}

pub(crate) fn granted_by(hash: &str) -> Option<String> {
    crate::util::lock(&GRANTED_BY)
        .as_ref()
        .and_then(|m| m.get(hash).cloned())
}

pub(crate) fn forget_granted_by(hash: &str) {
    if let Some(m) = crate::util::lock(&GRANTED_BY).as_mut() {
        m.remove(hash);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rec(state: MembershipState, submitted_at: u64) -> MembershipRecord {
        MembershipRecord {
            hash: "h".to_string(),
            identity: crate::sealed_store::format::IdentityBlock {
                registry_id: format!("logos:local:{}", "ab".repeat(32)),
                rln_identifier: String::new(),
                identity_commitment: "11".repeat(32),
                submitted_at,
            },
            cache: CacheState {
                state,
                leaf_index: Some(7),
                rate_limit: Some(300),
                ..CacheState::default()
            },
            alloc: crate::rate_limit::AllocationState::default(),
            quarantined: false,
        }
    }

    #[test]
    fn merge_state_matrix() {
        use MembershipState::*;
        let now = 10_000;
        assert_eq!(merge_state(None, None, now), Unknown);
        assert_eq!(merge_state(None, Some(Active), now), Active);
        let fresh = rec(Pending, now - 10);
        assert_eq!(merge_state(Some(&fresh), None, now), Pending);
        let stale = rec(Pending, now - CONFIRMATION_WINDOW_SECS - 1);
        assert_eq!(merge_state(Some(&stale), None, now), Failed);
        let unset = rec(Pending, 0);
        assert_eq!(merge_state(Some(&unset), None, now), Failed);
        let mut delegated = rec(Pending, now - CONFIRMATION_WINDOW_SECS - 1);
        delegated.cache.confirm_deadline = Some(now + 1);
        assert_eq!(merge_state(Some(&delegated), None, now), Pending);
        delegated.cache.confirm_deadline = Some(now - 1);
        assert_eq!(merge_state(Some(&delegated), None, now), Failed);
        assert_eq!(
            merge_state(Some(&stale), Some(GracePeriod), now),
            GracePeriod
        );
        let failed = rec(Failed, now - 1_000);
        assert_eq!(merge_state(Some(&failed), None, now), Failed);
        let was_active = rec(Active, now - 1_000);
        assert_eq!(merge_state(Some(&was_active), None, now), Erased);
        let mut ever_active = rec(Failed, now - 1_000);
        ever_active.cache.first_active_at = Some(now - 500);
        assert_eq!(merge_state(Some(&ever_active), None, now), Erased);
    }

    #[test]
    fn transition_event_gates_on_actual_state_change() {
        use MembershipState::*;
        let active = rec(Active, 0);
        assert!(transition_event("h", &active, active.cache.state, Active).is_none());

        let pending = rec(Pending, 0);
        let (registry_id, rln_identifier, hash, state, previous) =
            transition_event("h1", &pending, pending.cache.state, Active).expect("real transition");
        assert_eq!(registry_id, pending.identity.registry_id);
        assert_eq!(rln_identifier, "");
        assert_eq!(hash, "h1");
        assert_eq!(state, "active");
        assert_eq!(previous, "pending");

        let mut scoped = rec(Pending, 0);
        scoped.identity.rln_identifier = "ab".repeat(32);
        let (_, rln_identifier, ..) =
            transition_event("h2", &scoped, scoped.cache.state, Failed).expect("real transition");
        assert_eq!(rln_identifier, scoped.identity.rln_identifier);
    }

    #[test]
    fn first_active_at_semantics() {
        use MembershipState::*;
        let now = 10_000;
        let mut once_active = rec(Failed, now - 1_000);
        once_active.cache.first_active_at = Some(now - 500);
        assert_eq!(merge_state(Some(&once_active), None, now), Erased);
        let never_active = rec(Failed, now - 1_000);
        assert_eq!(merge_state(Some(&never_active), None, now), Failed);
    }

    #[test]
    fn async_submit_error_policy() {
        use MembershipState::*;
        let mut confirmed = rec(Active, 0).cache;
        confirmed.record_async_submit_error("boom", false);
        assert_eq!(confirmed.state, Active);
        assert!(confirmed.failed_reason.is_none());
        let mut retryable = rec(Pending, 0).cache;
        retryable.record_async_submit_error("boom", true);
        assert_eq!(retryable.state, Pending);
        assert!(retryable.failed_reason.is_none());
        let mut fatal = rec(Pending, 0).cache;
        fatal.record_async_submit_error("boom", false);
        assert_eq!(fatal.state, Failed);
        assert_eq!(fatal.failed_reason.as_deref(), Some("submit_failed: boom"));
        assert_eq!(fatal.retryable, Some(false));
    }

    #[test]
    fn grant_log_names_whoever_the_allocation_client_reported() {
        note_granted_by(
            "h1",
            &serde_json::json!({ "allocatorPeerId": "16Uiu2Found", "discovered": true }),
        );
        note_granted_by(
            "h2",
            &serde_json::json!({ "allocatorPeerId": "16Uiu2Fixed", "discovered": false }),
        );
        note_granted_by("h3", &serde_json::json!({ "leaf_index": 1 }));
        assert_eq!(
            granted_by("h1").as_deref(),
            Some("16Uiu2Found (discovered)")
        );
        assert_eq!(granted_by("h2").as_deref(), Some("16Uiu2Fixed"));
        assert!(granted_by("h3").is_none());
    }

    #[test]
    fn membership_state_wire_strings() {
        assert_eq!(
            serde_json::to_value(MembershipState::Unknown).unwrap(),
            serde_json::json!("unknown")
        );
        assert_eq!(
            serde_json::to_value(MembershipState::Pending).unwrap(),
            serde_json::json!("pending")
        );
        assert_eq!(
            serde_json::to_value(MembershipState::Failed).unwrap(),
            serde_json::json!("failed")
        );
        assert_eq!(
            serde_json::to_value(MembershipState::Active).unwrap(),
            serde_json::json!("active")
        );
        assert_eq!(
            serde_json::to_value(MembershipState::GracePeriod).unwrap(),
            serde_json::json!("grace_period")
        );
        assert_eq!(
            serde_json::to_value(MembershipState::Expired).unwrap(),
            serde_json::json!("expired")
        );
        assert_eq!(
            serde_json::to_value(MembershipState::ErasedAwaitsWithdrawal).unwrap(),
            serde_json::json!("erased_awaits_withdrawal")
        );
        assert_eq!(
            serde_json::to_value(MembershipState::Erased).unwrap(),
            serde_json::json!("erased")
        );
        assert_eq!(
            serde_json::to_value(MembershipState::Slashed).unwrap(),
            serde_json::json!("slashed")
        );
    }
}
