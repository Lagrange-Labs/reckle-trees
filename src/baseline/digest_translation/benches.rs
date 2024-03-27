use itertools::Itertools;
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::config::AlgebraicHasher;
use plonky2::plonk::config::GenericConfig;

use rand::rngs::StdRng;
use rand::SeedableRng;

use std::collections::HashMap;
use std::collections::HashSet;
use std::time::Instant;

use crate::baseline::digest_translation::binary_circuits::leaf_circuit_setup;

use crate::utils::helpers::generate_recproofs_leaves;
use crate::utils::helpers::get_pp_size_std;

pub fn dt_mono_worker<F, C, const D: usize>()
where
    C: GenericConfig<D, F = F> + 'static,
    F: RichField + Extendable<D>,
    C::Hasher: AlgebraicHasher<F>,
{
    let log_tree_sizes: Vec<u8> = vec![5];

    println!("=== Digest translation monolithic benches");
    println!("=== Warning: No proof compression, yet.");
    for log_tree_size in &log_tree_sizes {
        println!("===== Log tree size: {}", log_tree_size.clone());
        let log_tree_size = log_tree_size.clone();
        let tree_size: u32 = 1 << log_tree_size;
        let subset_indices: HashSet<u32> = HashSet::from_iter(0..tree_size);

        let mut r: StdRng = StdRng::seed_from_u64(223);
        let leaves: HashMap<u32, Vec<F>> = generate_recproofs_leaves(4, &mut r, &subset_indices);
        let leaves_monolith = leaves
            .into_iter()
            .sorted_by_key(|x| x.0)
            .map(|x| x.1)
            .collect_vec();

        println!("=== Done generating leaves");

        let now = Instant::now();
        let (wire_info_base, cd_base, pd_base, vd_base) =
            leaf_circuit_setup::<F, C, D>(log_tree_size, None);
        let elapsed = now.elapsed();
        println!("=== Setup done in {:?}", elapsed);

        get_pp_size_std(cd_base.clone(), &pd_base, vd_base.clone());
        let now = Instant::now();
        let pw = wire_info_base.compute_pw(&leaves_monolith);
        let proof = pd_base.prove(pw).unwrap();
        let elapsed = now.elapsed();
        println!("=== Prove done in {:?}", elapsed);

        let now = Instant::now();
        let result = vd_base.verify(proof).is_ok();
        let elapsed = now.elapsed();
        println!("=== Proof verification {:?} in {:?}", result, elapsed);
    }
}
