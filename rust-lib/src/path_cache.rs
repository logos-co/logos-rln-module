use std::collections::HashMap;
use std::sync::Mutex;

use crate::error::ApiError;
use crate::registry_id::CanonicalRegistryId;
use crate::tree::TreeSource;
use crate::util::lock;

struct CachedPath {
    path_elements_hex: Vec<String>,
    path_indices: Vec<u8>,
    leaf_index: u64,
    version: u64,
    /// Lifted Merkle root from the registry. Absent when a test planted the
    /// path; generate_proof then skips the accepted-root check.
    root: Option<[u8; 32]>,
}

struct PathSlot {
    published: Option<CachedPath>,
    /// Highest generation claimed for this membership. A fetch claims one
    /// before it reads the tree, so a slow older fetch cannot publish over
    /// a newer one.
    next_version: u64,
}

static PATHS: Mutex<Option<HashMap<String, PathSlot>>> = Mutex::new(None);

pub(crate) struct ServedPath {
    pub(crate) path_elements_hex: Vec<String>,
    pub(crate) path_indices: Vec<u8>,
    pub(crate) version: u64,
    pub(crate) root: Option<[u8; 32]>,
}

pub(crate) struct PreparedPath {
    pub(crate) path_elements_hex: Vec<String>,
    pub(crate) path_indices: Vec<u8>,
    pub(crate) leaf_index: u64,
    pub(crate) version: u64,
    pub(crate) root: Option<[u8; 32]>,
}

pub(crate) fn hit(hash: &str, current_leaf_index: u64) -> Option<ServedPath> {
    let guard = lock(&PATHS);
    let entry = guard.as_ref()?.get(hash)?.published.as_ref()?;
    (entry.leaf_index == current_leaf_index).then(|| ServedPath {
        path_elements_hex: entry.path_elements_hex.clone(),
        path_indices: entry.path_indices.clone(),
        version: entry.version,
        root: entry.root,
    })
}

fn claim_version(hash: &str) -> u64 {
    let mut guard = lock(&PATHS);
    let map = guard.get_or_insert_with(HashMap::new);
    let slot = map.entry(hash.to_string()).or_insert(PathSlot {
        published: None,
        next_version: 0,
    });
    slot.next_version = slot.next_version.saturating_add(1);
    slot.next_version
}

/// Fetch and adopt roots, but do not publish. The caller warms the partial
/// against this path, then `publish_path`, so proofs keep hitting the previous
/// path during the build.
pub(crate) fn fetch_path(
    registry: &CanonicalRegistryId,
    hash: &str,
    leaf_index: u64,
    tree: &dyn TreeSource,
) -> Result<PreparedPath, ApiError> {
    let version = claim_version(hash);
    let witness = tree.merkle_proof(registry, leaf_index)?.lifted();
    match witness.window {
        Some(window) => crate::roots::adopt(&registry.canonical, window),
        None => crate::roots::admit(&registry.canonical, witness.root),
    }
    Ok(PreparedPath {
        path_elements_hex: witness.path_elements_hex,
        path_indices: witness.path_indices,
        leaf_index,
        version,
        root: Some(witness.root),
    })
}

/// Publish `prepared` unless a newer generation is already visible.
pub(crate) fn publish_path(hash: &str, prepared: PreparedPath) -> bool {
    let mut guard = lock(&PATHS);
    let Some(slot) = guard.as_mut().and_then(|map| map.get_mut(hash)) else {
        return false;
    };
    if slot
        .published
        .as_ref()
        .is_some_and(|current| current.version > prepared.version)
    {
        return false;
    }
    slot.published = Some(CachedPath {
        path_elements_hex: prepared.path_elements_hex,
        path_indices: prepared.path_indices,
        leaf_index: prepared.leaf_index,
        version: prepared.version,
        root: prepared.root,
    });
    true
}

pub(crate) fn fill_path_cache(
    registry: &CanonicalRegistryId,
    hash: &str,
    leaf_index: u64,
    tree: &dyn TreeSource,
) -> Result<(), ApiError> {
    let prepared = fetch_path(registry, hash, leaf_index, tree)?;
    publish_path(hash, prepared);
    Ok(())
}

#[cfg(test)]
pub(crate) fn set_path_for_test(
    hash: &str,
    path_elements_hex: Vec<String>,
    path_indices: Vec<u8>,
    leaf_index: u64,
) {
    let version = claim_version(hash);
    publish_path(
        hash,
        PreparedPath {
            path_elements_hex,
            path_indices,
            leaf_index,
            version,
            root: None,
        },
    );
}

#[cfg(test)]
pub(crate) fn set_rooted_path_for_test(
    hash: &str,
    path_elements_hex: Vec<String>,
    path_indices: Vec<u8>,
    leaf_index: u64,
    root: [u8; 32],
) {
    let version = claim_version(hash);
    publish_path(
        hash,
        PreparedPath {
            path_elements_hex,
            path_indices,
            leaf_index,
            version,
            root: Some(root),
        },
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_proof_without_valid_roots_admits_its_root() {
        use crate::provider::fake::FakeTree;
        let _serial = lock(&crate::test_support::TEST_GLOBAL_LOCK);
        let registry = crate::registry_id::parse("fakens:local:admit-path").unwrap();
        let proof = serde_json::json!({
            "depth": 2, "leaf": "aa".repeat(32), "leaf_index": 3,
            "path_elements": ["cc".repeat(32), "dd".repeat(32)], "path_indices": [1, 0],
            "root": "bb".repeat(32),
        });
        let expected = crate::tree::MerkleProof::from_provider_json(&proof)
            .unwrap()
            .lifted()
            .root;
        let tree = FakeTree {
            proof: Some(proof),
            roots: None,
        };
        crate::roots::adopt(&registry.canonical, (1..=5).map(|n| [n; 32]).collect());

        fill_path_cache(&registry, "path-cache-test-admit", 3, &tree).expect("proof cached");

        let window = crate::roots::window(&registry.canonical).expect("window kept");
        assert_eq!(window.len(), 5);
        assert_eq!((window[0], window[1]), (expected, [1; 32]));
        let served = hit("path-cache-test-admit", 3).expect("path served");
        assert_eq!(
            served.root,
            Some(expected),
            "the slot keeps the lifted root"
        );
    }

    #[test]
    fn cold_hash_misses() {
        assert!(hit("path-cache-test-cold", 0).is_none());
    }

    #[test]
    fn fresh_entry_hits_leaf_mismatch_misses() {
        let hash = "path-cache-test-fresh";
        set_path_for_test(hash, vec!["ab".repeat(32)], vec![1], 5);
        let served = hit(hash, 5).expect("fresh entry served");
        assert_eq!(served.path_elements_hex, vec!["ab".repeat(32)]);
        assert_eq!(served.path_indices, vec![1]);

        assert!(
            hit(hash, 6).is_none(),
            "leaf_index mismatch must miss, never serve a stale path"
        );
    }

    #[test]
    fn refresh_overwrites_the_prior_entry() {
        let hash = "path-cache-test-refresh";
        set_path_for_test(hash, vec!["00".repeat(32)], vec![0], 1);
        set_path_for_test(hash, vec!["11".repeat(32)], vec![1], 2);

        let served = hit(hash, 2).expect("refreshed entry served");
        assert_eq!(served.path_elements_hex, vec!["11".repeat(32)]);
        assert_eq!(served.path_indices, vec![1]);
        assert!(
            hit(hash, 1).is_none(),
            "the old leaf_index's path is gone once the refresh overwrote it"
        );
    }

    #[test]
    fn an_older_publish_does_not_overwrite_a_newer_path() {
        let hash = "path-cache-test-version";
        let older = claim_version(hash);
        let newer = claim_version(hash);
        assert!(newer > older);
        assert!(publish_path(
            hash,
            PreparedPath {
                path_elements_hex: vec!["22".repeat(32)],
                path_indices: vec![1],
                leaf_index: 2,
                version: newer,
                root: Some([2; 32]),
            }
        ));
        assert!(
            !publish_path(
                hash,
                PreparedPath {
                    path_elements_hex: vec!["11".repeat(32)],
                    path_indices: vec![0],
                    leaf_index: 1,
                    version: older,
                    root: Some([1; 32]),
                }
            ),
            "a slow fetch must not publish over a newer generation"
        );
        let served = hit(hash, 2).expect("newer path stays visible");
        assert_eq!(served.path_elements_hex, vec!["22".repeat(32)]);
        assert_eq!(served.version, newer);
        assert_eq!(served.root, Some([2; 32]));
        assert!(hit(hash, 1).is_none());
    }
}
