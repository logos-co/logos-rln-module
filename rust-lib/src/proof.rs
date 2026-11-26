use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, LazyLock, Mutex};

use rand_chacha::ChaCha20Rng;
use rln::prelude::{
    compute_id_secret, graph_from_raw, hash_to_field_le, zkey_from_raw, ArkGroth16Backend,
    CanonicalDeserialize, CanonicalSerialize, Fr, Hasher, IdentityKeys, PartialProof, PoseidonHash,
    Proof, RLNBuilder, RLNMerkleProof, RLNPartialWitnessInput, RLNProof, RLNProofValues,
    RLNWitnessInput, SecretFr, Stateless, VerifyProofError, RLN,
};
use sha2::{Digest, Sha256};
use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};

use crate::registry_id::{bytes_to_hex, hex_decode_into, hex_to_bytes32, hex_to_vec};
use crate::util::lock;

pub(crate) const RLN_TREE_DEPTH: usize = 10;

const DEPTH_10_GRAPH: &[u8] = include_bytes!("../resources/tree_depth_10/graph.bin");
const DEPTH_10_ZKEY: &[u8] = include_bytes!("../resources/tree_depth_10/rln_final.arkzkey");

#[derive(Debug)]
pub(crate) enum ProofError {
    BadInput(String),
    Engine(String),
}

#[derive(Zeroize, ZeroizeOnDrop)]
pub(crate) struct WitnessMaterial {
    /// Names this membership's slot in the partial-proof cache.
    pub(crate) membership_hash: String,
    pub(crate) identity_secret_hash_hex: String,
    pub(crate) rate_limit: u64,
    pub(crate) message_id: u64,
    pub(crate) path_elements_hex: Vec<String>,
    pub(crate) path_indices: Vec<u8>,
    /// Monotonic generation of the path this witness was built from.
    /// Not part of the circuit input. `store_partial` refuses to replace a
    /// slot built from a newer generation.
    pub(crate) path_version: u64,
    /// `eviction_mark(membership_hash)`, taken before the credential was
    /// unsealed. Not part of the circuit input.
    pub(crate) eviction_mark: u64,
}

#[derive(Debug)]
pub(crate) struct RateLimitProof {
    canonical: Vec<u8>,
    root: [u8; 32],
    external_nullifier: [u8; 32],
    share_x: [u8; 32],
    share_y: [u8; 32],
    nullifier: [u8; 32],
    epoch: Option<u64>,
}

const GROTH16_LEN: usize = 128;

impl RateLimitProof {
    fn from_parts(proof: Proof, values: RLNProofValues) -> Result<Self, ProofError> {
        let (share_y, nullifier) = single_values(&values)?;
        let root = fr_to_bytes32(&values.root());
        let external_nullifier = fr_to_bytes32(&values.external_nullifier());
        let share_x = fr_to_bytes32(&values.x());
        let rln_proof = RLNProof::new(proof, values);
        let mut canonical = Vec::new();
        rln_proof
            .serialize_compressed(&mut canonical)
            .map_err(|e| ProofError::Engine(format!("serialize proof: {e}")))?;
        Ok(RateLimitProof {
            canonical,
            root,
            external_nullifier,
            share_x,
            share_y: fr_to_bytes32(&share_y),
            nullifier: fr_to_bytes32(&nullifier),
            epoch: None,
        })
    }

    pub(crate) fn root(&self) -> [u8; 32] {
        self.root
    }

    pub(crate) fn canonical_hex(&self) -> String {
        bytes_to_hex(&self.canonical)
    }

    pub(crate) fn to_json(&self) -> serde_json::Value {
        let mut out = serde_json::json!({
            "proof": bytes_to_hex(&self.canonical[..GROTH16_LEN.min(self.canonical.len())]),
            "root": bytes_to_hex(&self.root),
            "external_nullifier": bytes_to_hex(&self.external_nullifier),
            "share_x": bytes_to_hex(&self.share_x),
            "share_y": bytes_to_hex(&self.share_y),
            "nullifier": bytes_to_hex(&self.nullifier),
        });
        if let Some(epoch) = self.epoch {
            out["epoch"] = serde_json::Value::String(bytes_to_hex(&epoch_to_bytes(epoch)));
        }
        out
    }

    pub(crate) fn from_json(value: &serde_json::Value) -> Result<Self, ProofError> {
        let proof_hex = value
            .get("proof")
            .and_then(|v| v.as_str())
            .ok_or_else(|| ProofError::BadInput("proof: missing proof bytes".into()))?;
        let bytes = hex_to_vec(proof_hex)
            .ok_or_else(|| ProofError::BadInput("proof: not valid hex".into()))?;

        let canonical: Vec<u8> = if bytes.len() == GROTH16_LEN {
            let field = |key: &str| -> Result<Fr, ProofError> {
                let hex = value.get(key).and_then(|v| v.as_str()).ok_or_else(|| {
                    ProofError::BadInput(format!(
                        "{key}: expected 32-byte hex alongside a bare proof"
                    ))
                })?;
                hex_to_fr(hex, key)
            };
            let zk_proof = Proof::deserialize_compressed(&bytes[..]).map_err(|e| {
                ProofError::BadInput(format!("proof: not a valid Groth16 proof: {e}"))
            })?;
            let values = RLNProofValues::new_single()
                .y(field("share_y")?)
                .root(field("root")?)
                .nullifier(field("nullifier")?)
                .x(field("share_x")?)
                .external_nullifier(field("external_nullifier")?)
                .build();
            let rln_proof = RLNProof::new(zk_proof, values);
            let mut out = Vec::new();
            rln_proof
                .serialize_compressed(&mut out)
                .map_err(|e| ProofError::Engine(format!("serialize proof: {e}")))?;
            out
        } else {
            bytes
        };

        let epoch = match value.get("epoch") {
            None => None,
            Some(v) => {
                if let Some(index) = v.as_u64() {
                    Some(index)
                } else {
                    let hex = v.as_str().ok_or_else(|| {
                        ProofError::BadInput("epoch: expected 32-byte hex or u64 index".into())
                    })?;
                    let bytes = hex_to_bytes32(hex).ok_or_else(|| {
                        ProofError::BadInput("epoch: expected 32-byte hex or u64 index".into())
                    })?;
                    Some(epoch_from_bytes(&bytes).ok_or_else(|| {
                        ProofError::BadInput("epoch: non-canonical padding".into())
                    })?)
                }
            }
        };

        let rln_proof = parse_canonical(&canonical)?;
        let mut proof = Self::from_parts(rln_proof.proof, rln_proof.values)?;
        proof.epoch = epoch;
        Ok(proof)
    }

    pub(crate) fn external_nullifier(&self) -> [u8; 32] {
        self.external_nullifier
    }

    pub(crate) fn nullifier(&self) -> [u8; 32] {
        self.nullifier
    }

    pub(crate) fn share_x(&self) -> [u8; 32] {
        self.share_x
    }

    pub(crate) fn share_y(&self) -> [u8; 32] {
        self.share_y
    }

    pub(crate) fn epoch(&self) -> Option<u64> {
        self.epoch
    }

    fn to_rln_proof(&self) -> Result<RLNProof, ProofError> {
        parse_canonical(&self.canonical)
    }
}

static RLN_STATELESS: LazyLock<RLN<Stateless, ArkGroth16Backend<PoseidonHash>>> =
    LazyLock::new(|| {
        RLNBuilder::stateless()
            .graph(
                graph_from_raw(DEPTH_10_GRAPH, Some(RLN_TREE_DEPTH), None)
                    .expect("invariant: the vendored depth-10 graph loads at the circuit depth"),
            )
            .zkey(
                zkey_from_raw(DEPTH_10_ZKEY).expect("invariant: the vendored depth-10 zkey loads"),
            )
            .build()
    });

/// One partial proof per membership, over the part of the witness that stays
/// fixed between messages: identity secret, rate limit and Merkle path.
/// Groth16's blinding (r, s) is sampled fresh in `finish_proof`, so reusing a
/// partial proof across messages is sound; only the per-message inputs (x,
/// external nullifier, message_id) are proved each time. The partial proof is
/// derived from the identity secret, so it lives in memory only.
///
/// `fingerprint` covers the rate limit and path the partial was built from. A
/// refreshed path or a changed rate limit no longer matches, so the slot is
/// rebuilt instead of serving a stale partial. The identity secret is fixed
/// per membership, so the slot's key (the membership hash) already pins it.
struct CachedPartial {
    fingerprint: [u8; 32],
    /// Path-cache generation this partial was built from. An older build must
    /// not replace a newer one.
    path_version: u64,
    partial: Arc<PartialProof>,
    hits: u64,
}

static PARTIALS: Mutex<Option<HashMap<String, CachedPartial>>> = Mutex::new(None);

/// Per-slot eviction count. A build takes the slot's mark before it unseals
/// the credential and `store_partial` refuses it if the slot was evicted since,
/// so a proof or warm in flight across a lock cannot put the partial back.
/// Lock order: `PARTIALS` before `EVICTIONS`.
static EVICTIONS: Mutex<Option<HashMap<String, u64>>> = Mutex::new(None);

/// The slot's eviction mark. Take it before unsealing the credential.
pub(crate) fn eviction_mark(slot: &str) -> u64 {
    lock(&EVICTIONS)
        .as_ref()
        .and_then(|map| map.get(slot).copied())
        .unwrap_or(0)
}

static PARTIAL_HITS: AtomicU64 = AtomicU64::new(0);
static PARTIAL_MISSES: AtomicU64 = AtomicU64::new(0);
static PARTIAL_REFRESHES: AtomicU64 = AtomicU64::new(0);
static PARTIAL_FALLBACKS: AtomicU64 = AtomicU64::new(0);

#[cfg(test)]
thread_local! {
    static LOCAL_PARTIAL_HITS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Process-wide partial-proof cache counters: hits (finish_proof only),
/// misses (built on the proving path), refreshes (built ahead of use by the
/// poller), fallbacks (a full proof after a partial build or finish failed).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct PartialStats {
    pub(crate) hits: u64,
    pub(crate) misses: u64,
    pub(crate) refreshes: u64,
    pub(crate) fallbacks: u64,
}

pub(crate) fn partial_stats() -> PartialStats {
    PartialStats {
        hits: PARTIAL_HITS.load(Ordering::Relaxed),
        misses: PARTIAL_MISSES.load(Ordering::Relaxed),
        refreshes: PARTIAL_REFRESHES.load(Ordering::Relaxed),
        fallbacks: PARTIAL_FALLBACKS.load(Ordering::Relaxed),
    }
}

fn absorb(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

pub(crate) fn partial_fingerprint(
    rate_limit: u64,
    path_elements_hex: &[String],
    path_indices: &[u8],
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    absorb(&mut hasher, b"logos-rln-partial-proof-v1");
    absorb(&mut hasher, &rate_limit.to_le_bytes());
    absorb(&mut hasher, &(path_elements_hex.len() as u64).to_le_bytes());
    for element in path_elements_hex {
        absorb(&mut hasher, element.as_bytes());
    }
    absorb(&mut hasher, path_indices);
    hasher.finalize().into()
}

fn material_fingerprint(material: &WitnessMaterial) -> [u8; 32] {
    partial_fingerprint(
        material.rate_limit,
        &material.path_elements_hex,
        &material.path_indices,
    )
}

/// The slot's partial if it was built from this exact fingerprint.
/// Cloning the `Arc` does not copy the partial's mask.
fn cached_partial(slot: &str, fingerprint: &[u8; 32]) -> Option<Arc<PartialProof>> {
    let guard = lock(&PARTIALS);
    let entry = guard.as_ref()?.get(slot)?;
    (&entry.fingerprint == fingerprint).then(|| Arc::clone(&entry.partial))
}

/// Insert `partial` unless the slot was evicted after `eviction_mark` was
/// taken, or already holds one built from a newer path generation. Returns
/// whether the slot was replaced.
fn store_partial(
    slot: &str,
    fingerprint: [u8; 32],
    partial: Arc<PartialProof>,
    path_version: u64,
    eviction_mark: u64,
) -> bool {
    let mut guard = lock(&PARTIALS);
    let evictions = lock(&EVICTIONS)
        .as_ref()
        .and_then(|map| map.get(slot).copied())
        .unwrap_or(0);
    if evictions != eviction_mark {
        return false;
    }
    let map = guard.get_or_insert_with(HashMap::new);
    if map
        .get(slot)
        .is_some_and(|existing| existing.path_version > path_version)
    {
        return false;
    }
    map.insert(
        slot.to_string(),
        CachedPartial {
            fingerprint,
            path_version,
            partial,
            hits: 0,
        },
    );
    true
}

/// Raise the slot's path generation when the path was refreshed but its
/// fingerprint did not change, so an in-flight build of an older generation
/// cannot overwrite it.
pub(crate) fn adopt_path_version(slot: &str, fingerprint: &[u8; 32], path_version: u64) {
    let mut guard = lock(&PARTIALS);
    let Some(entry) = guard.as_mut().and_then(|map| map.get_mut(slot)) else {
        return;
    };
    if &entry.fingerprint == fingerprint && path_version > entry.path_version {
        entry.path_version = path_version;
    }
}

fn note_hit(slot: &str, fingerprint: &[u8; 32]) {
    {
        let mut guard = lock(&PARTIALS);
        if let Some(entry) = guard.as_mut().and_then(|map| map.get_mut(slot)) {
            if &entry.fingerprint == fingerprint {
                entry.hits += 1;
            }
        }
    }
    PARTIAL_HITS.fetch_add(1, Ordering::Relaxed);
    #[cfg(test)]
    LOCAL_PARTIAL_HITS.with(|count| count.set(count.get() + 1));
}

/// Drop the slot only when it still holds the fingerprint that failed.
/// A newer refresh may have replaced it while `finish_proof` was running.
fn drop_partial_if(slot: &str, fingerprint: &[u8; 32]) {
    let mut guard = lock(&PARTIALS);
    let Some(map) = guard.as_mut() else {
        return;
    };
    if map
        .get(slot)
        .is_some_and(|entry| &entry.fingerprint == fingerprint)
    {
        map.remove(slot);
    }
}

pub(crate) fn evict_partial(hash: &str) {
    evict_partials(std::iter::once(hash));
}

/// Drop these memberships' partials and bump their eviction marks, so a build
/// that unsealed before the eviction cannot store afterwards. The map removal
/// is the zeroization boundary: `PartialProof` does not implement `Zeroize`.
pub(crate) fn evict_partials<'a>(hashes: impl IntoIterator<Item = &'a str>) {
    let mut guard = lock(&PARTIALS);
    let mut evictions = lock(&EVICTIONS);
    let evictions = evictions.get_or_insert_with(HashMap::new);
    for hash in hashes {
        if let Some(map) = guard.as_mut() {
            map.remove(hash);
        }
        let count = evictions.entry(hash.to_string()).or_insert(0);
        *count = count.wrapping_add(1);
    }
}

pub(crate) fn partial_matches(slot: &str, fingerprint: &[u8; 32]) -> bool {
    lock(&PARTIALS)
        .as_ref()
        .and_then(|map| map.get(slot))
        .is_some_and(|entry| &entry.fingerprint == fingerprint)
}

/// Whether `slot` holds a partial built from this rate limit and path.
#[cfg(test)]
pub(crate) fn partial_is_current(
    slot: &str,
    rate_limit: u64,
    path_elements_hex: &[String],
    path_indices: &[u8],
) -> bool {
    partial_matches(
        slot,
        &partial_fingerprint(rate_limit, path_elements_hex, path_indices),
    )
}

/// Build and cache the membership's partial proof ahead of use, so the first
/// proof after a path change only runs `finish_proof`. Returns whether a new
/// partial was stored (false when the slot was already current, or a newer
/// generation won the race).
#[cfg(test)]
pub(crate) fn warm_partial(material: &WitnessMaterial) -> Result<bool, ProofError> {
    warm_with_fingerprint(material, material_fingerprint(material))
}

pub(crate) fn warm_with_fingerprint(
    material: &WitnessMaterial,
    fingerprint: [u8; 32],
) -> Result<bool, ProofError> {
    let slot = material.membership_hash.as_str();
    if partial_matches(slot, &fingerprint) {
        adopt_path_version(slot, &fingerprint, material.path_version);
        return Ok(false);
    }
    // x and the external nullifier are not part of the partial witness, so any
    // value serves here.
    let witness = build_witness(material, Fr::from(0u64), Fr::from(0u64))?;
    let partial = RLN_STATELESS
        .generate_partial_proof(&RLNPartialWitnessInput::from(&witness))
        .map_err(|e| ProofError::Engine(format!("generate partial: {e}")))?;
    let stored = store_partial(
        slot,
        fingerprint,
        Arc::new(partial),
        material.path_version,
        material.eviction_mark,
    );
    if stored {
        PARTIAL_REFRESHES.fetch_add(1, Ordering::Relaxed);
    }
    Ok(stored)
}

/// Prove with the membership's cached partial when it matches, building it on
/// a miss. A failed finish drops the slot only if it still holds the
/// fingerprint that failed, then falls back to a full proof, so a bad cache
/// entry costs time and never fails a send.
fn prove(
    material: &WitnessMaterial,
    witness: &RLNWitnessInput,
) -> Result<(Proof, RLNProofValues), ProofError> {
    let slot = material.membership_hash.as_str();
    let fingerprint = material_fingerprint(material);
    let (partial, from_cache) = match cached_partial(slot, &fingerprint) {
        Some(partial) => (partial, true),
        None => {
            PARTIAL_MISSES.fetch_add(1, Ordering::Relaxed);
            match RLN_STATELESS.generate_partial_proof(&RLNPartialWitnessInput::from(witness)) {
                Ok(partial) => (Arc::new(partial), false),
                Err(e) => {
                    PARTIAL_FALLBACKS.fetch_add(1, Ordering::Relaxed);
                    eprintln!("rln proof: {slot} partial proof build failed, proving in full: {e}");
                    return RLN_STATELESS
                        .generate_proof(witness)
                        .map_err(|err| ProofError::Engine(format!("generate: {err}")));
                }
            }
        }
    };
    match RLN_STATELESS.finish_proof(&partial, witness) {
        Ok(done) => {
            if from_cache {
                note_hit(slot, &fingerprint);
            } else {
                // Store only after finish succeeds, so a partial that cannot
                // be finished never occupies the slot.
                store_partial(
                    slot,
                    fingerprint,
                    partial,
                    material.path_version,
                    material.eviction_mark,
                );
            }
            Ok(done)
        }
        Err(e) => {
            PARTIAL_FALLBACKS.fetch_add(1, Ordering::Relaxed);
            if from_cache {
                drop_partial_if(slot, &fingerprint);
            }
            eprintln!("rln proof: {slot} finish_proof failed, proving in full: {e}");
            RLN_STATELESS
                .generate_proof(witness)
                .map_err(|err| ProofError::Engine(format!("generate: {err}")))
        }
    }
}

#[cfg(test)]
pub(crate) fn partial_hits(slot: &str) -> Option<u64> {
    lock(&PARTIALS).as_ref()?.get(slot).map(|e| e.hits)
}

#[cfg(test)]
pub(crate) fn partial_slot_fingerprint(slot: &str) -> Option<[u8; 32]> {
    lock(&PARTIALS).as_ref()?.get(slot).map(|e| e.fingerprint)
}

/// Finish-equivalent for tests: count one hit without running `finish_proof`,
/// so a kept slot (hits stay) is distinct from a rebuilt one (hits reset to 0).
#[cfg(test)]
pub(crate) fn touch_partial_for_test(slot: &str) {
    let fingerprint = partial_slot_fingerprint(slot).expect("slot exists");
    cached_partial(slot, &fingerprint).expect("slot current");
    note_hit(slot, &fingerprint);
}

#[cfg(test)]
pub(crate) fn local_partial_hits() -> u64 {
    LOCAL_PARTIAL_HITS.with(std::cell::Cell::get)
}

#[cfg(test)]
pub(crate) fn clone_slot_for_test(from: &str, to: &str) {
    let fingerprint = partial_slot_fingerprint(from).expect("source slot");
    let partial = cached_partial(from, &fingerprint).expect("source partial");
    let version = lock(&PARTIALS)
        .as_ref()
        .and_then(|map| map.get(from))
        .map(|entry| entry.path_version)
        .expect("source slot");
    assert!(
        store_partial(to, fingerprint, partial, version, eviction_mark(to)),
        "bystander slot stored"
    );
}

fn single_values(values: &RLNProofValues) -> Result<(Fr, Fr), ProofError> {
    match (values.y(), values.nullifier()) {
        (Some(y), Some(nullifier)) => Ok((y, nullifier)),
        _ => Err(ProofError::Engine(
            "multi-mode proof values unsupported".into(),
        )),
    }
}

fn parse_canonical(bytes: &[u8]) -> Result<RLNProof, ProofError> {
    let rln_proof = RLNProof::deserialize_compressed(bytes)
        .map_err(|e| ProofError::BadInput(format!("proof: not a valid RLN proof: {e}")))?;
    if rln_proof.values.y().is_none() {
        return Err(ProofError::BadInput(
            "proof: multi-mode proofs are not supported".into(),
        ));
    }
    Ok(rln_proof)
}

fn epoch_to_bytes(epoch: u64) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[..8].copy_from_slice(&epoch.to_le_bytes());
    out
}

pub(crate) fn epoch_from_bytes(bytes: &[u8; 32]) -> Option<u64> {
    if bytes[8..32].iter().any(|&b| b != 0) {
        return None;
    }
    Some(u64::from_le_bytes(
        bytes[..8]
            .try_into()
            .expect("invariant: an 8-byte range converts to [u8; 8]"),
    ))
}

fn external_nullifier(epoch: u64, rln_identifier: &[u8; 32]) -> Fr {
    let epoch_fr = hash_to_field_le(&epoch_to_bytes(epoch));
    let rln_identifier_fr = hash_to_field_le(rln_identifier);
    Hasher::<PoseidonHash>::hash_pair(epoch_fr, rln_identifier_fr)
}

pub(crate) use rln_signal::signal_to_x;

pub(crate) fn x_from_hash_hex(hex: &str) -> Result<Fr, ProofError> {
    hex_to_fr(hex, "signal_hash")
}

pub(crate) fn expected_external_nullifier(epoch: u64, rln_identifier: &[u8; 32]) -> [u8; 32] {
    fr_to_bytes32(&external_nullifier(epoch, rln_identifier))
}

fn fr_to_bytes32(fr: &Fr) -> [u8; 32] {
    let mut out = [0u8; 32];
    fr.serialize_compressed(&mut out[..])
        .expect("invariant: Fr's canonical LE form is exactly 32 bytes");
    out
}

fn secret_to_bytes32(secret: &SecretFr) -> [u8; 32] {
    let mut out = [0u8; 32];
    write_secret_bytes32(secret, &mut out);
    out
}

fn write_secret_bytes32(secret: &SecretFr, out: &mut [u8; 32]) {
    secret
        .serialize_compressed(&mut out[..])
        .expect("invariant: SecretFr's canonical LE form is exactly 32 bytes");
}

pub(crate) mod depth_bridge {
    use super::{
        CanonicalDeserialize, CanonicalSerialize, Fr, Hasher, PoseidonHash, RLN_TREE_DEPTH,
    };
    use crate::registry_id::{bytes_to_hex, hex_to_bytes32};
    use std::sync::LazyLock;

    static ZERO_LADDER: LazyLock<Vec<Fr>> = LazyLock::new(|| {
        let mut ladder = vec![Fr::from(0u64)];
        for height in 1..=RLN_TREE_DEPTH {
            let below = ladder[height - 1];
            ladder.push(Hasher::<PoseidonHash>::hash_pair(below, below));
        }
        ladder
    });

    fn fr_to_hex(value: &Fr) -> String {
        let mut bytes = [0u8; 32];
        value
            .serialize_compressed(&mut bytes[..])
            .expect("invariant: a field element serializes into 32 bytes");
        bytes_to_hex(&bytes)
    }

    fn fr_from_hex(hex: &str) -> Option<Fr> {
        let bytes = hex_to_bytes32(hex)?;
        Fr::deserialize_compressed(&bytes[..]).ok()
    }

    pub(crate) fn pad_path(elements: &mut Vec<String>, indices: &mut Vec<u8>, depth: usize) {
        for height in depth..RLN_TREE_DEPTH {
            elements.push(fr_to_hex(&ZERO_LADDER[height]));
            indices.push(0);
        }
    }

    pub(crate) fn fold_root(root_hex: &str, depth: usize) -> String {
        let Some(mut root) = fr_from_hex(root_hex) else {
            return root_hex.to_string();
        };
        for height in depth..RLN_TREE_DEPTH {
            root = Hasher::<PoseidonHash>::hash_pair(root, ZERO_LADDER[height]);
        }
        fr_to_hex(&root)
    }
}

fn hex_to_fr(hex: &str, label: &str) -> Result<Fr, ProofError> {
    let bytes = hex_to_bytes32(hex)
        .ok_or_else(|| ProofError::BadInput(format!("{label}: expected 32-byte hex")))?;
    Fr::deserialize_compressed(&bytes[..])
        .map_err(|e| ProofError::BadInput(format!("{label}: not a field element: {e}")))
}

pub(crate) fn generate_identity() -> Result<(String, String), ProofError> {
    let mut seed = [0u8; 32];
    getrandom::getrandom(&mut seed).map_err(|e| ProofError::Engine(format!("rng: {e}")))?;
    let keys = IdentityKeys::generate_seeded::<PoseidonHash, ChaCha20Rng>(&seed);
    seed.zeroize();
    let mut secret_bytes = Zeroizing::new([0u8; 32]);
    write_secret_bytes32(&keys.identity_secret(), &mut secret_bytes);
    Ok((
        bytes_to_hex(&fr_to_bytes32(&keys.id_commitment())),
        bytes_to_hex(&secret_bytes[..]),
    ))
}

pub(crate) fn generate(
    material: &WitnessMaterial,
    x: Fr,
    epoch: u64,
    rln_identifier: &[u8; 32],
) -> Result<RateLimitProof, ProofError> {
    let witness = build_witness(material, x, external_nullifier(epoch, rln_identifier))?;
    let (proof, values) = prove(material, &witness)?;
    let mut rlp = RateLimitProof::from_parts(proof, values)?;
    rlp.epoch = Some(epoch);
    Ok(rlp)
}

fn build_witness(
    material: &WitnessMaterial,
    x: Fr,
    external_nullifier: Fr,
) -> Result<RLNWitnessInput, ProofError> {
    if material.path_elements_hex.len() != material.path_indices.len() {
        return Err(ProofError::BadInput(format!(
            "merkle path length mismatch: {} elements vs {} indices",
            material.path_elements_hex.len(),
            material.path_indices.len()
        )));
    }
    if material.path_elements_hex.len() != RLN_TREE_DEPTH {
        return Err(ProofError::BadInput(format!(
            "merkle path depth {} != circuit depth {RLN_TREE_DEPTH}",
            material.path_elements_hex.len()
        )));
    }

    let mut secret_bytes = Zeroizing::new([0u8; 32]);
    if !hex_decode_into(&material.identity_secret_hash_hex, &mut secret_bytes[..]) {
        return Err(ProofError::BadInput(
            "identity_secret_hash: expected 32-byte hex".into(),
        ));
    }
    let identity_secret = SecretFr::deserialize_compressed(&secret_bytes[..])
        .map_err(|e| ProofError::BadInput(format!("identity_secret: {e}")))?;

    let path_elements = material
        .path_elements_hex
        .iter()
        .map(|h| hex_to_fr(h, "path_element"))
        .collect::<Result<Vec<Fr>, _>>()?;

    RLNWitnessInput::new_single()
        .identity_secret(identity_secret)
        .user_message_limit(Fr::from(material.rate_limit))
        .message_id(Fr::from(material.message_id))
        .merkle_proof(RLNMerkleProof::new(
            path_elements,
            material.path_indices.clone(),
        ))
        .x(x)
        .external_nullifier(external_nullifier)
        .build()
        .map_err(|e| ProofError::BadInput(format!("witness: {e}")))
}

pub(crate) fn verify(
    proof: &RateLimitProof,
    x: Fr,
    valid_roots: &[[u8; 32]],
) -> Result<bool, ProofError> {
    let rln_proof = proof.to_rln_proof()?;
    let roots: Vec<Fr> = valid_roots
        .iter()
        .filter_map(|r| Fr::deserialize_compressed(&r[..]).ok())
        .collect();
    if !valid_roots.is_empty() && roots.is_empty() {
        return Ok(false);
    }

    match RLN_STATELESS.verify_with_roots(&rln_proof.proof, &rln_proof.values, &x, &roots) {
        Ok(verdict) => Ok(verdict),
        Err(VerifyProofError::InvalidRoot | VerifyProofError::InvalidSignal) => Ok(false),
        Err(e) => Err(ProofError::Engine(format!("verify: {e}"))),
    }
}

pub(crate) fn recover_identity_secret_hex(
    prior: ([u8; 32], [u8; 32]),
    current: ([u8; 32], [u8; 32]),
) -> Result<String, ProofError> {
    let field = |bytes: &[u8; 32], label: &str| -> Result<Fr, ProofError> {
        Fr::deserialize_compressed(&bytes[..])
            .map_err(|e| ProofError::BadInput(format!("{label}: not a field element: {e}")))
    };
    let share1 = (
        field(&prior.0, "prior share_x")?,
        field(&prior.1, "prior share_y")?,
    );
    let share2 = (field(&current.0, "share_x")?, field(&current.1, "share_y")?);
    let secret = compute_id_secret(share1, share2)
        .map_err(|e| ProofError::Engine(format!("recover id secret: {e}")))?;
    Ok(bytes_to_hex(&secret_to_bytes32(&secret)))
}

#[cfg(test)]
pub(crate) fn generate_for_test(
    seed: &[u8],
    signal: &[u8],
    epoch: u64,
    rln_identifier: &[u8; 32],
) -> RateLimitProof {
    let keys = IdentityKeys::generate_seeded::<PoseidonHash, ChaCha20Rng>(seed);
    let material = WitnessMaterial {
        membership_hash: bytes_to_hex(&fr_to_bytes32(&keys.id_commitment())),
        identity_secret_hash_hex: bytes_to_hex(&secret_to_bytes32(&keys.identity_secret())),
        rate_limit: 100,
        message_id: 0,
        path_elements_hex: vec!["00".repeat(32); RLN_TREE_DEPTH],
        path_indices: vec![0u8; RLN_TREE_DEPTH],
        path_version: 0,
        eviction_mark: 0,
    };
    generate(&material, signal_to_x(signal), epoch, rln_identifier).expect("test proof")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn zero_path() -> (Vec<String>, Vec<u8>) {
        let elements = vec!["00".repeat(32); RLN_TREE_DEPTH];
        let indices = vec![0u8; RLN_TREE_DEPTH];
        (elements, indices)
    }

    fn material_from_seed(seed: &[u8], rate_limit: u64, message_id: u64) -> WitnessMaterial {
        let keys = IdentityKeys::generate_seeded::<PoseidonHash, ChaCha20Rng>(seed);
        let secret_hex = bytes_to_hex(&secret_to_bytes32(&keys.identity_secret()));
        let (elements, indices) = zero_path();
        WitnessMaterial {
            membership_hash: bytes_to_hex(&fr_to_bytes32(&keys.id_commitment())),
            identity_secret_hash_hex: secret_hex,
            rate_limit,
            message_id,
            path_elements_hex: elements,
            path_indices: indices,
            path_version: 0,
            eviction_mark: 0,
        }
    }

    #[test]
    fn padding_and_folding_agree() {
        use crate::registry_id::bytes_to_hex;

        const REGISTRY_DEPTH: usize = 9;

        let leaf = Hasher::<PoseidonHash>::hash_pair(Fr::from(11u64), Fr::from(22u64));
        let mut elements: Vec<String> = (0..REGISTRY_DEPTH)
            .map(|i| {
                let mut buf = [0u8; 32];
                Fr::from(i as u64 + 7)
                    .serialize_compressed(&mut buf[..])
                    .expect("32 bytes");
                bytes_to_hex(&buf)
            })
            .collect();
        let mut indices = vec![0u8; REGISTRY_DEPTH];

        let fold_through = |leaf: Fr, elements: &[String], indices: &[u8]| -> Fr {
            let mut node = leaf;
            for (hex, &is_right) in elements.iter().zip(indices) {
                let sibling = hex_to_fr(hex, "sibling").expect("test sibling");
                node = if is_right == 0 {
                    Hasher::<PoseidonHash>::hash_pair(node, sibling)
                } else {
                    Hasher::<PoseidonHash>::hash_pair(sibling, node)
                };
            }
            node
        };

        let registry_root = fold_through(leaf, &elements, &indices);
        let mut root_bytes = [0u8; 32];
        registry_root
            .serialize_compressed(&mut root_bytes[..])
            .expect("32 bytes");

        let lifted = depth_bridge::fold_root(&bytes_to_hex(&root_bytes), REGISTRY_DEPTH);
        depth_bridge::pad_path(&mut elements, &mut indices, REGISTRY_DEPTH);
        assert_eq!(elements.len(), RLN_TREE_DEPTH);
        assert_eq!(indices.len(), RLN_TREE_DEPTH);

        let through_padded = fold_through(leaf, &elements, &indices);
        let mut padded_bytes = [0u8; 32];
        through_padded
            .serialize_compressed(&mut padded_bytes[..])
            .expect("32 bytes");

        assert_eq!(
            lifted,
            bytes_to_hex(&padded_bytes),
            "a lifted root must equal the root the padded path folds to"
        );
    }

    #[test]
    fn padding_a_full_depth_path_changes_nothing() {
        let (mut elements, mut indices) = zero_path();
        let before = elements.clone();
        depth_bridge::pad_path(&mut elements, &mut indices, RLN_TREE_DEPTH);
        assert_eq!(elements, before);
        assert_eq!(elements.len(), RLN_TREE_DEPTH);

        let root = "00".repeat(32);
        assert_eq!(depth_bridge::fold_root(&root, RLN_TREE_DEPTH), root);
    }

    #[test]
    fn prehashed_signal_round_trips_and_rejects_non_canonical() {
        let x = signal_to_x(b"Hello, RLN!");
        let hex = bytes_to_hex(&fr_to_bytes32(&x));
        assert_eq!(x_from_hash_hex(&hex).expect("canonical"), x);
        assert_eq!(
            x_from_hash_hex(&format!("0x{hex}")).expect("0x tolerated"),
            x
        );
        assert_eq!(fr_to_bytes32(&x), rln_signal::signal_hash(b"Hello, RLN!"));

        assert!(matches!(
            x_from_hash_hex(&"ff".repeat(32)),
            Err(ProofError::BadInput(m)) if m.contains("signal_hash")
        ));
        assert!(matches!(
            x_from_hash_hex(&"ab".repeat(31)),
            Err(ProofError::BadInput(_))
        ));
        assert!(matches!(
            x_from_hash_hex("zz"),
            Err(ProofError::BadInput(_))
        ));
    }

    #[test]
    fn frozen_interop_vectors() {
        let keys = IdentityKeys::generate_seeded::<PoseidonHash, ChaCha20Rng>(&[7u8; 32]);
        assert_eq!(
            bytes_to_hex(&secret_to_bytes32(&keys.identity_secret())),
            "3c87aa7480ec2cad022ef39c256ddb6e4fb083c7d4a0dfdc4eee891feda7a62b"
        );
        assert_eq!(
            bytes_to_hex(&fr_to_bytes32(&keys.id_commitment())),
            "08772427f3a88a9787e8f899c13dc10c2b0a226d7500c99edba0f993ba770729"
        );

        let rln_id = [9u8; 32];
        assert_eq!(
            bytes_to_hex(&fr_to_bytes32(&external_nullifier(1231028105, &rln_id))),
            "a432bb300aeda21d8c14186e134639ecac20732e9ebcbb73139741cef293612a"
        );

        assert_eq!(
            bytes_to_hex(&fr_to_bytes32(&signal_to_x(b"Hello, RLN!"))),
            "9af96b554db1bc4bfb806f3bcd587c8c0ee80d4d79c440a87b51861235461412"
        );

        let material = material_from_seed(&[7u8; 32], 100, 0);
        let j = generate(&material, signal_to_x(b"Hello, RLN!"), 1231028105, &rln_id)
            .expect("generate")
            .to_json();
        assert_eq!(
            j["root"].as_str().unwrap(),
            "16f5e233ad4c8ee7d66d1b0909f942e3384eb12721296690d340cc77ff41aa1b"
        );
        assert_eq!(
            j["nullifier"].as_str().unwrap(),
            "0d78806341fee59517f2526662095294eee5f590be3c36d9e7d29680b73aa21a"
        );
        assert_eq!(
            j["share_x"].as_str().unwrap(),
            "9af96b554db1bc4bfb806f3bcd587c8c0ee80d4d79c440a87b51861235461412"
        );
        assert_eq!(
            j["epoch"].as_str().unwrap(),
            "89ff5f4900000000000000000000000000000000000000000000000000000000"
        );

        let j2 = generate(
            &material_from_seed(&[7u8; 32], 100, 1),
            signal_to_x(b"Hello, RLN!"),
            1231028105,
            &rln_id,
        )
        .expect("generate mid=1")
        .to_json();
        assert_eq!(
            j2["nullifier"].as_str().unwrap(),
            "cbf8daa2f4d16e31165c6789a738681b0871a5cc775206af276ad4295e185e1e"
        );

        let bare = hex_to_vec(j["proof"].as_str().unwrap()).unwrap();
        assert_eq!(bare.len(), 128, "to_json emits the bare spec proof[128]");
    }

    #[test]
    fn generate_then_verify_roundtrips() {
        let material = material_from_seed(&[7u8; 32], 100, 0);
        let rln_id = [9u8; 32];
        let proof =
            generate(&material, signal_to_x(b"hello"), 1231028105, &rln_id).expect("generate");
        let root = proof.root();
        assert!(verify(&proof, signal_to_x(b"hello"), &[root]).expect("verify"));
    }

    // Each test uses its own seed, so its own membership slot: the cache is
    // process-wide and tests run in parallel.

    #[test]
    fn the_cached_partial_is_reused_and_proofs_are_still_reblinded() {
        let rln_id = [9u8; 32];
        let first = material_from_seed(&[42u8; 32], 100, 0);
        let second = material_from_seed(&[42u8; 32], 100, 1);
        let a = generate(&first, signal_to_x(b"one"), 77, &rln_id).expect("generate a");
        assert_eq!(
            partial_hits(&first.membership_hash),
            Some(0),
            "first proof builds the slot"
        );
        let b = generate(&second, signal_to_x(b"two"), 77, &rln_id).expect("generate b");
        let c = generate(&second, signal_to_x(b"two"), 77, &rln_id).expect("generate c");
        assert_eq!(
            partial_hits(&first.membership_hash),
            Some(2),
            "later proofs for the same membership and path finish the cached partial"
        );
        assert!(verify(&a, signal_to_x(b"one"), &[a.root()]).expect("verify a"));
        assert!(verify(&b, signal_to_x(b"two"), &[b.root()]).expect("verify b"));
        assert!(verify(&c, signal_to_x(b"two"), &[c.root()]).expect("verify c"));
        assert_ne!(
            a.nullifier(),
            b.nullifier(),
            "message_id still binds the nullifier"
        );
        assert_ne!(
            b.canonical, c.canonical,
            "finish_proof re-blinds, so equal inputs give distinct proofs"
        );
    }

    #[test]
    fn a_changed_path_replaces_the_membership_slot() {
        let rln_id = [9u8; 32];
        let mut moved = material_from_seed(&[43u8; 32], 100, 0);
        let a = generate(&moved, signal_to_x(b"m"), 5, &rln_id).expect("generate a");
        generate(&moved, signal_to_x(b"m2"), 5, &rln_id).expect("warm hit");
        assert_eq!(partial_hits(&moved.membership_hash), Some(1));

        let mut buf = [0u8; 32];
        Fr::from(5u64)
            .serialize_compressed(&mut buf[..])
            .expect("32 bytes");
        moved.path_elements_hex[0] = bytes_to_hex(&buf);
        assert!(!partial_is_current(
            &moved.membership_hash,
            moved.rate_limit,
            &moved.path_elements_hex,
            &moved.path_indices
        ));
        let b = generate(&moved, signal_to_x(b"m"), 5, &rln_id).expect("generate b");
        assert_eq!(
            partial_hits(&moved.membership_hash),
            Some(0),
            "the new path rebuilt the slot instead of finishing the old partial"
        );
        assert_ne!(
            a.root(),
            b.root(),
            "the new path proves against its own root"
        );
        assert!(verify(&b, signal_to_x(b"m"), &[b.root()]).expect("verify b"));
        assert!(!verify(&b, signal_to_x(b"m"), &[a.root()]).expect("verify b vs old root"));
    }

    #[test]
    fn a_changed_path_index_replaces_the_membership_slot() {
        let rln_id = [9u8; 32];
        let mut moved = material_from_seed(&[47u8; 32], 100, 0);
        generate(&moved, signal_to_x(b"i"), 5, &rln_id).expect("generate a");
        generate(&moved, signal_to_x(b"i2"), 5, &rln_id).expect("warm hit");
        assert_eq!(partial_hits(&moved.membership_hash), Some(1));
        let before = partial_slot_fingerprint(&moved.membership_hash).expect("slot");

        moved.path_indices[0] = 1;
        assert!(!partial_is_current(
            &moved.membership_hash,
            moved.rate_limit,
            &moved.path_elements_hex,
            &moved.path_indices
        ));
        let proved = generate(&moved, signal_to_x(b"i"), 5, &rln_id).expect("generate b");
        assert_eq!(
            partial_hits(&moved.membership_hash),
            Some(0),
            "flipping a path index rebuilt the slot"
        );
        assert_ne!(
            partial_slot_fingerprint(&moved.membership_hash),
            Some(before),
            "the index is part of the fingerprint"
        );
        assert!(verify(&proved, signal_to_x(b"i"), &[proved.root()]).expect("verify"));
    }

    #[test]
    fn a_changed_rate_limit_replaces_the_membership_slot() {
        let rln_id = [9u8; 32];
        let mut m = material_from_seed(&[45u8; 32], 100, 0);
        generate(&m, signal_to_x(b"r"), 5, &rln_id).expect("generate at 100");
        generate(&m, signal_to_x(b"r2"), 5, &rln_id).expect("hit at 100");
        assert_eq!(partial_hits(&m.membership_hash), Some(1));
        let before = partial_slot_fingerprint(&m.membership_hash).expect("slot at 100");

        m.rate_limit = 20;
        let p = generate(&m, signal_to_x(b"r"), 5, &rln_id).expect("generate at 20");
        assert_eq!(
            partial_hits(&m.membership_hash),
            Some(0),
            "rebuilt for the new limit"
        );
        assert_ne!(
            partial_slot_fingerprint(&m.membership_hash),
            Some(before),
            "the new limit replaced the fingerprint"
        );
        assert!(verify(&p, signal_to_x(b"r"), &[p.root()]).expect("verify"));
    }

    #[test]
    fn warm_partial_builds_ahead_of_use() {
        let rln_id = [9u8; 32];
        let m = material_from_seed(&[44u8; 32], 100, 0);
        assert_eq!(partial_hits(&m.membership_hash), None);
        assert!(warm_partial(&m).expect("warm"), "a cold slot is built");
        assert!(
            !warm_partial(&m).expect("warm again"),
            "a current slot is left alone"
        );
        let p = generate(&m, signal_to_x(b"w"), 9, &rln_id).expect("generate");
        assert_eq!(
            partial_hits(&m.membership_hash),
            Some(1),
            "the first proof after warming already hits"
        );
        assert!(verify(&p, signal_to_x(b"w"), &[p.root()]).expect("verify"));
    }

    #[test]
    fn a_corrupt_partial_falls_back_to_a_full_proof() {
        let _serial = crate::lock(&crate::test_support::TEST_GLOBAL_LOCK);
        let rln_id = [9u8; 32];
        let m = material_from_seed(&[46u8; 32], 100, 0);
        warm_partial(&m).expect("warm");
        let fingerprint = material_fingerprint(&m);
        let mut bad =
            (*cached_partial(&m.membership_hash, &fingerprint).expect("warmed slot")).clone();
        bad.mask.clear();
        assert!(store_partial(
            &m.membership_hash,
            fingerprint,
            Arc::new(bad),
            m.path_version,
            m.eviction_mark
        ));

        let fallbacks_before = partial_stats().fallbacks;
        let hits_before = local_partial_hits();
        let p = generate(&m, signal_to_x(b"f"), 3, &rln_id).expect("falls back, never fails");
        assert!(verify(&p, signal_to_x(b"f"), &[p.root()]).expect("verify"));
        assert_eq!(
            partial_hits(&m.membership_hash),
            None,
            "the failed slot is dropped so the next proof rebuilds it"
        );
        assert_eq!(
            partial_stats().fallbacks,
            fallbacks_before + 1,
            "the failed finish counts as a fallback"
        );
        assert_eq!(
            local_partial_hits(),
            hits_before,
            "the failed finish is not counted as a hit"
        );
    }

    #[test]
    fn a_build_that_unsealed_before_an_eviction_does_not_store() {
        let rln_id = [9u8; 32];
        let mut m = material_from_seed(&[50u8; 32], 100, 0);
        m.eviction_mark = eviction_mark(&m.membership_hash);
        // The keystore locks while this build holds the unsealed secret.
        evict_partial(&m.membership_hash);

        assert!(
            !warm_partial(&m).expect("warm"),
            "a warm that unsealed before the lock must not store"
        );
        let p = generate(&m, signal_to_x(b"e"), 4, &rln_id).expect("still proves");
        assert!(verify(&p, signal_to_x(b"e"), &[p.root()]).expect("verify"));
        assert_eq!(
            partial_slot_fingerprint(&m.membership_hash),
            None,
            "a proof that unsealed before the lock must not store either"
        );

        m.eviction_mark = eviction_mark(&m.membership_hash);
        assert!(
            warm_partial(&m).expect("warm"),
            "a build that unsealed after the eviction stores again"
        );
    }

    #[test]
    fn store_partial_refuses_an_older_path_version() {
        let mut m = material_from_seed(&[48u8; 32], 100, 0);
        m.path_version = 2;
        warm_partial(&m).expect("warm");
        touch_partial_for_test(&m.membership_hash);
        let fingerprint = partial_slot_fingerprint(&m.membership_hash).expect("slot");
        let partial = cached_partial(&m.membership_hash, &fingerprint).expect("partial");
        let other = [9u8; 32];

        assert!(
            !store_partial(&m.membership_hash, other, Arc::clone(&partial), 1, 0),
            "an older generation must not replace the slot"
        );
        assert_eq!(
            partial_slot_fingerprint(&m.membership_hash),
            Some(fingerprint)
        );
        assert_eq!(partial_hits(&m.membership_hash), Some(1));

        assert!(store_partial(&m.membership_hash, other, partial, 2, 0));
        assert_eq!(partial_slot_fingerprint(&m.membership_hash), Some(other));
        assert_eq!(
            partial_hits(&m.membership_hash),
            Some(0),
            "an accepted replace resets the hit count"
        );
    }

    #[test]
    fn drop_partial_if_removes_only_the_fingerprint_that_failed() {
        let m = material_from_seed(&[49u8; 32], 100, 0);
        warm_partial(&m).expect("warm");
        let fingerprint = partial_slot_fingerprint(&m.membership_hash).expect("slot");

        drop_partial_if(&m.membership_hash, &[0u8; 32]);
        assert_eq!(
            partial_slot_fingerprint(&m.membership_hash),
            Some(fingerprint),
            "a different fingerprint leaves the slot in place"
        );

        drop_partial_if(&m.membership_hash, &fingerprint);
        assert_eq!(partial_slot_fingerprint(&m.membership_hash), None);
    }

    #[test]
    fn wrong_signal_is_invalid_not_error() {
        let material = material_from_seed(&[7u8; 32], 100, 0);
        let rln_id = [9u8; 32];
        let proof =
            generate(&material, signal_to_x(b"hello"), 1231028105, &rln_id).expect("generate");
        let root = proof.root();
        assert!(!verify(&proof, signal_to_x(b"goodbye"), &[root]).expect("verify"));
    }

    #[test]
    fn root_outside_window_is_invalid() {
        let rln_id = [9u8; 32];
        let a = generate(
            &material_from_seed(&[7u8; 32], 100, 0),
            signal_to_x(b"hello"),
            1,
            &rln_id,
        )
        .expect("generate a");
        let b = generate(
            &material_from_seed(&[8u8; 32], 100, 0),
            signal_to_x(b"hello"),
            1,
            &rln_id,
        )
        .expect("generate b");
        assert_ne!(a.root(), b.root());
        assert!(!verify(&a, signal_to_x(b"hello"), &[b.root()]).expect("verify"));
        assert!(!verify(&a, signal_to_x(b"hello"), &[[0xffu8; 32]]).expect("verify non-canonical"));
    }

    #[test]
    fn decomposed_spec_struct_roundtrip_verifies() {
        let material = material_from_seed(&[5u8; 32], 100, 2);
        let rln_id = [6u8; 32];
        let proof = generate(&material, signal_to_x(b"net msg"), 77, &rln_id).expect("generate");
        let root = proof.root();
        let j = proof.to_json();

        let decomposed = serde_json::json!({
            "proof": j["proof"],
            "root": j["root"],
            "external_nullifier": j["external_nullifier"],
            "share_x": j["share_x"],
            "share_y": j["share_y"],
            "nullifier": j["nullifier"],
        });

        let restored = RateLimitProof::from_json(&decomposed).expect("decomposed from_json");
        assert_eq!(restored.root(), root);
        assert_eq!(
            restored.to_json()["proof"],
            j["proof"],
            "reconstruction must be byte-identical to the canonical form"
        );
        assert!(verify(&restored, signal_to_x(b"net msg"), &[root]).expect("verify"));

        let mut bad = decomposed;
        bad["share_y"] = serde_json::json!("11".repeat(32));
        match RateLimitProof::from_json(&bad) {
            Err(_) => {}
            Ok(p) => {
                assert!(!verify(&p, signal_to_x(b"net msg"), &[root]).expect("verify tampered"))
            }
        }
    }

    #[test]
    fn canonical_blob_alone_round_trips() {
        let material = material_from_seed(&[5u8; 32], 100, 2);
        let rln_id = [6u8; 32];
        let proof = generate(&material, signal_to_x(b"net msg"), 77, &rln_id).expect("generate");
        let hex = proof.canonical_hex();
        assert_eq!(
            hex.len(),
            289 * 2,
            "Single-mode canonical blob is 289 bytes"
        );
        assert!(
            hex.starts_with(proof.to_json()["proof"].as_str().unwrap()),
            "the blob's leading segment is the bare proof[128]"
        );

        let restored = RateLimitProof::from_json(&serde_json::json!({ "proof": hex }))
            .expect("blob-only from_json");
        assert_eq!(restored.root(), proof.root());
        assert!(verify(&restored, signal_to_x(b"net msg"), &[proof.root()]).expect("verify"));
    }

    #[test]
    fn json_roundtrip_preserves_verification() {
        let material = material_from_seed(&[3u8; 32], 100, 1);
        let rln_id = [4u8; 32];
        let proof = generate(&material, signal_to_x(b"signal"), 42, &rln_id).expect("generate");
        let root = proof.root();
        let json = proof.to_json();
        let restored = RateLimitProof::from_json(&json).expect("from_json");
        assert_eq!(restored.root(), root);
        assert_eq!(proof.epoch(), Some(42));
        assert_eq!(
            restored.epoch(),
            Some(42),
            "the epoch survives the round trip"
        );
        assert!(verify(&restored, signal_to_x(b"signal"), &[root]).expect("verify"));
    }

    #[test]
    fn message_id_at_or_above_rate_limit_is_bad_input() {
        let material = material_from_seed(&[1u8; 32], 5, 5);
        let err = generate(&material, signal_to_x(b"x"), 1, &[0u8; 32]).unwrap_err();
        assert!(matches!(err, ProofError::BadInput(_)));
    }

    #[test]
    fn short_merkle_path_is_bad_input() {
        let mut material = material_from_seed(&[1u8; 32], 100, 0);
        material.path_elements_hex.truncate(RLN_TREE_DEPTH - 1);
        material.path_indices.truncate(RLN_TREE_DEPTH - 1);
        let err = generate(&material, signal_to_x(b"x"), 1, &[0u8; 32]).unwrap_err();
        assert!(matches!(err, ProofError::BadInput(_)));
    }

    #[test]
    fn epoch_from_bytes_rejects_non_canonical_padding() {
        let canonical = epoch_to_bytes(1231028105);
        assert_eq!(epoch_from_bytes(&canonical), Some(1231028105));

        let mut tampered = canonical;
        tampered[20] = 0xff;
        assert_eq!(epoch_from_bytes(&tampered), None);
    }

    #[test]
    fn from_json_accepts_numeric_epoch_from_the_handler_reply() {
        let material = material_from_seed(&[3u8; 32], 100, 1);
        let rln_id = [4u8; 32];
        let proof = generate(&material, signal_to_x(b"signal"), 42, &rln_id).expect("generate");

        let mut wire = proof.to_json();
        wire["epoch"] = serde_json::json!(42u64);
        let restored = RateLimitProof::from_json(&wire).expect("from_json");
        assert_eq!(restored.epoch(), Some(42));

        wire["epoch"] = serde_json::json!(-1);
        assert!(matches!(
            RateLimitProof::from_json(&wire).unwrap_err(),
            ProofError::BadInput(_)
        ));
    }

    #[test]
    fn recover_identity_secret_from_colliding_shares() {
        let rln_id = [9u8; 32];
        let a = generate_for_test(&[7u8; 32], b"signal-A", 1231028105, &rln_id);
        let b = generate_for_test(&[7u8; 32], b"signal-B", 1231028105, &rln_id);
        assert_eq!(
            a.nullifier(),
            b.nullifier(),
            "same identity+epoch+slot ⇒ one nullifier"
        );
        assert_ne!(
            a.share_x(),
            b.share_x(),
            "distinct signals ⇒ distinct share_x"
        );

        let secret =
            recover_identity_secret_hex((a.share_x(), a.share_y()), (b.share_x(), b.share_y()))
                .expect("recover");
        assert_eq!(
            secret,
            "3c87aa7480ec2cad022ef39c256ddb6e4fb083c7d4a0dfdc4eee891feda7a62b"
        );
    }

    #[test]
    fn witness_material_is_zeroized_on_drop() {
        fn wiped_on_drop<T: zeroize::ZeroizeOnDrop>() {}
        wiped_on_drop::<WitnessMaterial>();
    }
}
