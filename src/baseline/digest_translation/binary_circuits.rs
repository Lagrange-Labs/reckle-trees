use itertools::Itertools;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CommonCircuitData, ProverCircuitData, VerifierCircuitData},
        config::{AlgebraicHasher, GenericConfig},
    },
};
use plonky2_crypto::hash::keccak256::CircuitBuilderHashKeccak;

use crate::baseline::digest_translation::wire_information::WireInformation;
use crate::utils::helpers::{concate_keccak_input, convert_hashout_to_biguint};

pub fn leaf_circuit_setup<F, C, const D: usize>(
    log_tree_size: u8,
    _min_degree_bits: Option<&usize>,
) -> (
    WireInformation<D>,
    CommonCircuitData<F, D>,
    ProverCircuitData<F, C, D>,
    VerifierCircuitData<F, C, D>,
)
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    C::Hasher: AlgebraicHasher<F>,
{
    let log_tree_size = log_tree_size as usize;
    let tree_size = (1 << log_tree_size) as usize;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());

    let mut poseidon_merkle = vec![builder.add_virtual_hashes(tree_size)];
    let mut keccak_merkle = vec![poseidon_merkle[0]
        .iter()
        .map(|x| convert_hashout_to_biguint(&mut builder, &x))
        .collect_vec()];

    for i in 1..=log_tree_size {
        let size = 1 << (log_tree_size - i);
        let subtree_level = (0..size)
            .map(|j| {
                builder.hash_or_noop::<C::Hasher>(
                    [
                        poseidon_merkle[i - 1][2 * j].elements.to_vec(),
                        poseidon_merkle[i - 1][2 * j + 1].elements.to_vec(),
                    ]
                    .concat(),
                )
            })
            .collect_vec();
        poseidon_merkle.push(subtree_level);
    }

    for i in 1..=log_tree_size {
        let size = 1 << (log_tree_size - i);
        let subtree_level = (0..size)
            .map(|j| {
                let concat_left_right = concate_keccak_input(
                    &mut builder,
                    256,
                    keccak_merkle[i - 1][2 * j].clone(),
                    keccak_merkle[i - 1][2 * j + 1].clone(),
                );
                builder.hash_keccak256(&concat_left_right)
            })
            .collect_vec();
        keccak_merkle.push(subtree_level);
    }

    builder.register_public_inputs(&poseidon_merkle[log_tree_size][0].elements);

    for i in &keccak_merkle[log_tree_size][0].limbs {
        builder.register_public_input(i.0);
    }
    builder.print_gate_counts(0);

    let data = builder.build::<C>();
    let wire_information = WireInformation::<D>::new(&poseidon_merkle[0]);
    let common_data = data.verifier_data().common;
    let verifier_data = data.verifier_data();
    let prover_data = data.prover_data();

    (wire_information, common_data, prover_data, verifier_data)
}

mod tests {
    #[test]
    fn dt_mono_benches() {
        env_logger::init();
        log::set_max_level(log::LevelFilter::Debug);

        const D: usize = 2;
        type C = plonky2::plonk::config::PoseidonGoldilocksConfig;
        type F = <C as plonky2::plonk::config::GenericConfig<D>>::F;

        crate::baseline::digest_translation::benches::dt_mono_worker::<F, C, D>();
    }
}
