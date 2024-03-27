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

use crate::reckle_std::binary_pp::SNARK_PP;
use crate::reckle_std::binary_tree::RecDS;
use crate::utils::canonical::CanonicalTree;
use crate::utils::mt_binary::{MerkleProof, PartialMT};

pub fn rec_worker<F, C, const D: usize>()
where
    C::Hasher: AlgebraicHasher<F>,
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
{
    let mut r: StdRng = StdRng::seed_from_u64(223);
    let log_tree_sizes: Vec<u8> = vec![10];
    let log_subset_sizes: Vec<u32> = vec![4];

    for log_tree_size in &log_tree_sizes {
        println!("=== Tree size: {}", log_tree_size.clone());
        let log_tree_size = log_tree_size.clone();
        let tree_size: u32 = 1 << log_tree_size;

        let pp: SNARK_PP<F, C, D>;

        let now = Instant::now();
        pp = SNARK_PP::<F, C, D>::setup(log_tree_size);
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

            let leaves: HashMap<u32, Vec<F>> = subset_indices
                .clone()
                .into_iter()
                .map(|i| (i as u32, F::rand_vec(5)))
                .collect::<HashMap<_, _>>();

            let mt = PartialMT::<F, C::Hasher>::new(log_tree_size, &leaves);
            println!("=== Partial Merkle tree done");

            let mut merkle_proofs: HashMap<u32, (Vec<F>, MerkleProof<F, C::Hasher>)> =
                HashMap::new();
            for (k, v) in &leaves {
                let mt_proof = mt.prove(*k);
                merkle_proofs.insert(*k, (v.clone(), mt_proof));
            }
            println!("=== Get individual proofs of the subset");

            let mut rec_ds: RecDS<F, C, D>;
            let now = Instant::now();
            rec_ds = RecDS::<F, C, D>::new(&pp, merkle_proofs);
            let elapsed = now.elapsed();

            println!("=== Prove done in {:?}", elapsed);

            let now = Instant::now();
            _ = CanonicalTree::<F, C::Hasher>::new(log_tree_size, &leaves);
            let elapsed = now.elapsed();
            println!("=== Canonical digest computed in {:?}", elapsed);

            let recproofs_verifier = pp.get_verifier();
            let recproof = rec_ds.get_recproof();
            let proof = recproof.clone();
            let now = Instant::now();
            let _ = recproofs_verifier.verify(proof);
            let elapsed = now.elapsed();
            println!("=== Proof verified in {:?} (w/o canonical)", elapsed);

            let now = Instant::now();
            let updated_index = subset_indices.iter().choose(&mut r).unwrap().clone();
            println!("=== Updating index {:?}", updated_index);

            let updated_value = F::rand_vec(4);
            rec_ds.update_tree(&pp, updated_index, updated_value);
            let elapsed = now.elapsed();
            println!("=== Update done to an index in {:?}", elapsed);

            let recproof = rec_ds.get_recproof();
            let _ = recproofs_verifier.verify(recproof);
            println!("=== Updated proof verified");

            println!("=== Proof sizes");
            rec_ds.size_by_level(&pp, updated_index);

            println!("=== Public parameter sizes");
            pp.size_by_level();
        }
    }
}
