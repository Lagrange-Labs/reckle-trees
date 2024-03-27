use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::config::AlgebraicHasher;
use plonky2::plonk::config::GenericConfig;

use rand::rngs::StdRng;
use rand::seq::IteratorRandom;
use rand::SeedableRng;

use std::collections::HashMap;
use std::collections::HashSet;
use std::time::Instant;

use crate::reckle_bucket::binary_pp::SNARK_PP;
use crate::reckle_bucket::binary_tree::BucketDS;

use crate::utils::canonical::CanonicalTree;
use crate::utils::helpers::{generate_leaf_value, generate_recproofs_leaves};

pub fn bucket_worker<const Q: usize, F, C, const D: usize>()
where
    C: GenericConfig<D, F = F> + 'static,
    F: RichField + Extendable<D>,
    C::Hasher: AlgebraicHasher<F>,
    [(); 1 << Q]:,
{
    let mut r: StdRng = StdRng::seed_from_u64(223);
    let log_tree_sizes: Vec<u8> = vec![10];
    let log_subset_sizes: Vec<u32> = vec![4];

    println!("=== Log bucket size: {}", Q);
    for log_tree_size in &log_tree_sizes {
        assert!(Q < (*log_tree_size as usize));
        println!("=== Log tree size: {}", log_tree_size.clone());
        let log_tree_size = log_tree_size.clone();
        let tree_size: u32 = 1 << log_tree_size;

        let pp: SNARK_PP<Q, F, C, D>;

        let now = Instant::now();
        pp = SNARK_PP::<Q, F, C, D>::setup(log_tree_size);
        let elapsed = now.elapsed();
        println!("=== Setup done in {:?}", elapsed);

        for log_subset_size in &log_subset_sizes {
            println!(
                "=== Subset size: {}/{}",
                log_subset_size.clone(),
                log_tree_size.clone()
            );
            let subset_indices: HashSet<u32> = HashSet::from_iter(
                (0..tree_size).choose_multiple(&mut r, (1 << log_subset_size) as usize),
            );

            let leaves: HashMap<u32, Vec<F>> =
                generate_recproofs_leaves(4, &mut r, &subset_indices);
            let leaves_copy = leaves.clone();

            let mut bucket_ds: BucketDS<Q, F, C, D>;
            let now = Instant::now();
            bucket_ds = BucketDS::<Q, F, C, D>::new(log_tree_size, &pp, leaves);
            let elapsed = now.elapsed();
            println!("=== Prove done in {:?}", elapsed);

            let now = Instant::now();
            _ = CanonicalTree::<F, C::Hasher>::new(log_tree_size, &leaves_copy);
            let elapsed = now.elapsed();
            println!("=== Canonical digest computed in {:?}", elapsed);

            let recproofs_verifier = pp.get_verifier();
            let recproof = bucket_ds.get_recproof();
            let proof = recproof.clone();
            let now = Instant::now();
            let _ = recproofs_verifier.verify(proof);
            let elapsed = now.elapsed();
            println!("=== Proof verified in {:?} (w/o canonical)", elapsed);

            let now = Instant::now();
            let updated_index = subset_indices.iter().choose(&mut r).unwrap().clone();
            println!("=== Updating index {:?}", updated_index);

            let updated_value = generate_leaf_value(4, &mut r, updated_index);
            bucket_ds.update_tree(&pp, updated_index, updated_value);
            let elapsed = now.elapsed();
            println!("=== Update done to an index in {:?}", elapsed);

            let recproof = bucket_ds.get_recproof();
            let _ = recproofs_verifier.verify(recproof);
            println!("=== Updated proof verified");

            println!("=== Proof sizes");
            bucket_ds.size_by_level(&pp, updated_index);

            println!("=== Public parameter sizes");
            pp.size_by_level();
        }
    }
}
