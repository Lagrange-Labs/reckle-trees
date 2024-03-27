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
use plonky2_bn254::curves::g1curve_target::G1Target;

use crate::{
    baseline::bls::wire_information::WireInformation, bls::BN254_TO_U32_LIMBS,
    utils::helpers::merkle_select,
};

pub fn circuit_setup<F, C, const D: usize>(
    log_tree_size: u8,
    log_subset_size: u8,
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
    let subset_size = 1 << log_subset_size;

    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());

    let digest_t = builder.add_virtual_hash();

    let index_t = builder.add_virtual_targets(subset_size);

    let pk_u32 = (0..subset_size)
        .map(|_| builder.add_virtual_targets(BN254_TO_U32_LIMBS))
        .collect_vec();
    let pk_t = pk_u32
        .iter()
        .map(|x| G1Target::from_vec(&mut builder, &x))
        .collect_vec();
    let pk_hash_t = pk_u32
        .iter()
        .map(|x| builder.hash_or_noop::<C::Hasher>(x.to_vec()))
        .collect_vec();
    let result_pk_t = pk_t
        .into_iter()
        .reduce(|a, b| a.add(&mut builder, &b))
        .unwrap();

    let proof_t = (0..subset_size)
        .into_iter()
        .map(|_| builder.add_virtual_hashes(log_tree_size))
        .collect_vec();
    let index_bits_t = (0..subset_size)
        .into_iter()
        .map(|i| builder.split_le(index_t[i], log_tree_size))
        .collect_vec();

    for i in 0..subset_size {
        let mut current_digest_t = pk_hash_t[i];
        for j in 0..log_tree_size {
            let (left, right) = merkle_select(
                &mut builder,
                index_bits_t[i][j],
                proof_t[i][j],
                current_digest_t,
            );
            let preimage_t = [left.elements.to_vec(), right.elements.to_vec()].concat();
            current_digest_t = builder.hash_or_noop::<C::Hasher>(preimage_t.clone());
        }
        builder.connect_hashes(current_digest_t, digest_t);
    }

    builder.register_public_inputs(&digest_t.elements);
    builder.register_public_inputs(&result_pk_t.to_vec());
    builder.print_gate_counts(0);

    let data = builder.build::<C>();

    let wire_information = WireInformation::<D>::new(digest_t, &index_t, &pk_u32, &proof_t);
    let common_data = data.verifier_data().common;
    let verifier_data = data.verifier_data();
    let prover_data = data.prover_data();

    (wire_information, common_data, prover_data, verifier_data)
}
#[cfg(test)]
mod tests {

    use log::LevelFilter;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    use crate::baseline::bls::benches::bls_mono_worker;

    #[test]
    fn bls_mono_benches() {
        env_logger::init();
        log::set_max_level(LevelFilter::Debug);

        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        bls_mono_worker::<F, C, D>();
    }
}
