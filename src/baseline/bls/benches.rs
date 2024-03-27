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

use crate::baseline::bls::binary_circuits::circuit_setup;
use crate::utils::helpers::generate_bls_pks;
use crate::utils::helpers::get_pp_size_ecc;
use crate::utils::mt_binary::PartialMT;

pub fn bls_mono_worker<F, C, const D: usize>()
where
    C: GenericConfig<D, F = F> + 'static,
    F: RichField + Extendable<D>,
    C::Hasher: AlgebraicHasher<F>,
{
    println!("=== BLS monolithic benches");
    println!("=== Warning: No proof compression, yet.");
    let mut r: StdRng = StdRng::seed_from_u64(223);
    let log_tree_sizes: Vec<u8> = vec![5];
    let log_subset_sizes: Vec<u8> = vec![4];

    for log_tree_size in &log_tree_sizes {
        println!("===== Log tree size: {}", log_tree_size.clone());
        let log_tree_size = log_tree_size.clone();
        let tree_size: u32 = 1 << log_tree_size;

        for log_subset_size in &log_subset_sizes {
            println!(
                "=== Subset size: {}/{}",
                log_subset_size.clone(),
                log_tree_size.clone()
            );
            let subset_indices: HashSet<u32> = HashSet::from_iter(
                (0..tree_size).choose_multiple(&mut r, (1 << log_subset_size) as usize),
            );
            let leaves: HashMap<u32, Vec<F>> = generate_bls_pks::<F>(&mut r, &subset_indices);
            let mt = PartialMT::<F, C::Hasher>::new(log_tree_size as u8, &leaves);
            let mt_digest = mt.get_digest();
            println!("=== Partial Merkle tree done");

            let mut merkle_proofs = HashMap::new();
            for (k, v) in &leaves {
                let mt_proof = mt.prove(*k);
                merkle_proofs.insert(*k, (v.clone(), mt_proof));
            }
            println!("=== Get individual proofs of the subset");

            let now = Instant::now();
            let (wire_info_base, cd_base, pd_base, vd_base) =
                circuit_setup::<F, C, D>(log_tree_size, log_subset_size.clone(), None);
            let elapsed = now.elapsed();
            println!("=== Setup done in {:?}", elapsed);

            get_pp_size_ecc(cd_base.clone(), &pd_base, vd_base.clone());

            let now = Instant::now();
            let pw = wire_info_base.compute_pw::<F, C::Hasher>(mt_digest, &merkle_proofs);
            let proof = pd_base.prove(pw).unwrap();
            let elapsed = now.elapsed();
            println!("=== Prove done in {:?}", elapsed);

            let now = Instant::now();
            let result = vd_base.verify(proof).is_ok();
            let elapsed = now.elapsed();
            println!("=== Proof verification {:?} in {:?}", result, elapsed);
        }
    }
}
