use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, Hasher};

use rand::rngs::StdRng;
use rand::Rng;
use rand::SeedableRng;

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use crate::digest_translation::binary_pp::SNARK_PP;
use crate::digest_translation::binary_tree::DigestTranslationDS;

use crate::utils::helpers::{generate_leaf_value, generate_recproofs_leaves};

pub fn dt_worker<F, C, KH, PH, const D: usize>()
where
    C: GenericConfig<D, F = F> + 'static,
    F: RichField + Extendable<D>,
    C::Hasher: AlgebraicHasher<F>,
    KH: Hasher<F>,
    PH: AlgebraicHasher<F>,
{
    let log_tree_sizes: Vec<u8> = vec![5];

    for log_tree_size in &log_tree_sizes {
        println!("=== Tree size: {}", log_tree_size.clone());
        let log_tree_size = log_tree_size.clone();
        let tree_size: u32 = 1 << log_tree_size;
        let subset_indices: HashSet<u32> = HashSet::from_iter(0..tree_size);

        let mut r: StdRng = StdRng::seed_from_u64(223);
        let leaves: HashMap<u32, Vec<F>> = generate_recproofs_leaves(4, &mut r, &subset_indices);

        let now = Instant::now();
        let pp = SNARK_PP::<F, C, D>::setup::<KH, PH>(log_tree_size);
        let elapsed = now.elapsed();
        println!("=== Setup done in {:?}", elapsed);

        let now = Instant::now();
        let mut dt_ds = DigestTranslationDS::<F, C, KH, PH, D>::new(&pp, leaves);
        let elapsed = now.elapsed();
        println!("=== Prove done in {:?}", elapsed);

        let compact_proof_level = pp.compaction_level - 1;
        let now = Instant::now();
        let result = pp.verifier_compact[compact_proof_level.clone() as usize]
            .verify(dt_ds.proofs_compact[&compact_proof_level].clone())
            .is_ok();
        let elapsed = now.elapsed();
        println!("=== Proof verification {:?} in {:?}", result, elapsed);

        let updated_index = r.gen_range(0..tree_size);
        let updated_value = generate_leaf_value(4, &mut r, updated_index);

        let now = Instant::now();
        dt_ds.update_tree(&pp, updated_index, updated_value);
        let elapsed = now.elapsed();
        println!(
            "=== Update done to index {:?} in {:?}",
            updated_index, elapsed
        );

        println!("=== Proof sizes");
        dt_ds.size_by_level(&pp, updated_index);

        println!("=== Public parameter sizes");
        pp.size_by_level();
    }
}
