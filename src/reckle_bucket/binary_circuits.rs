use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::{HashOut, RichField};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{
    CircuitConfig, CommonCircuitData, ProverCircuitData, VerifierCircuitData,
};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig};

use itertools::Itertools;

use crate::reckle_bucket::wire_information::{
    CompactWireInformation, InternalWireInformation, LeafWireInformation,
};
use crate::reckle_std;
use crate::utils::helpers::{compute_root_canonical, conditional_equal_hash, is_hash_zero};

pub fn leaf_circuit_setup<const Q: usize, F, C, const D: usize>(
    _min_degree_bits: Option<&usize>,
) -> (
    LeafWireInformation<Q, D>,
    CommonCircuitData<F, D>,
    ProverCircuitData<F, C, D>,
    VerifierCircuitData<F, C, D>,
)
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    C::Hasher: AlgebraicHasher<F>,
    [(); 1 << Q]:,
{
    let log_bucket_size = Q;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());

    let mut subtree_merkle = vec![builder.add_virtual_hashes(1 << log_bucket_size)];
    for i in 1..=log_bucket_size {
        let size = 1 << (log_bucket_size - i);
        let subtree_level = (0..size)
            .map(|j| {
                builder.hash_or_noop::<C::Hasher>(
                    [
                        subtree_merkle[i - 1][2 * j].elements.to_vec(),
                        subtree_merkle[i - 1][2 * j + 1].elements.to_vec(),
                    ]
                    .concat(),
                )
            })
            .collect_vec();
        subtree_merkle.push(subtree_level);
    }

    let mut subtree_canonical = vec![builder.add_virtual_hashes(1 << log_bucket_size)];

    let mut is_canonical_non_zero = vec![(0..(1 << log_bucket_size))
        .map(|i| {
            let is_canonical_zero = is_hash_zero(&mut builder, subtree_canonical[0][i]);
            let is_canonical_non_zero = builder.not(is_canonical_zero);
            conditional_equal_hash(
                &mut builder,
                is_canonical_non_zero,
                subtree_canonical[0][i],
                subtree_merkle[0][i],
            );
            is_canonical_non_zero
        })
        .collect_vec()];

    for i in 1..=log_bucket_size {
        let size = 1 << (log_bucket_size - i);

        let canonical_level = (0..size)
            .map(|j| {
                let selector = builder.and(
                    is_canonical_non_zero[i - 1][2 * j],
                    is_canonical_non_zero[i - 1][2 * j + 1],
                );
                compute_root_canonical::<F, C, D>(
                    &mut builder,
                    selector,
                    subtree_canonical[i - 1][2 * j],
                    subtree_canonical[i - 1][2 * j + 1],
                )
            })
            .collect_vec();
        subtree_canonical.push(canonical_level);

        let is_canonical_non_zero_level = (0..size)
            .map(|j| {
                let is_canonical_zero = is_hash_zero(&mut builder, subtree_canonical[i][j]);
                builder.not(is_canonical_zero)
            })
            .collect_vec();
        is_canonical_non_zero.push(is_canonical_non_zero_level);
    }

    builder.register_public_inputs(&subtree_merkle[log_bucket_size][0].elements);
    builder.register_public_inputs(&subtree_canonical[log_bucket_size][0].elements);

    builder.print_gate_counts(0);

    let data = builder.build::<C>();
    let wire_information =
        LeafWireInformation::<Q, D>::new(&subtree_merkle[0], &subtree_canonical[0]);
    let common_data = data.verifier_data().common;
    let verifier_data = data.verifier_data();
    let prover_data = data.prover_data();

    (wire_information, common_data, prover_data, verifier_data)
}

pub fn internal_circuit_setup<F, C, InnerC, const D: usize>(
    inner_cd: &CommonCircuitData<F, D>,
    prev_circuit_digest: HashOut<F>,
    min_degree_bits: Option<&usize>,
) -> (
    InternalWireInformation<D>,
    CommonCircuitData<F, D>,
    ProverCircuitData<F, C, D>,
    VerifierCircuitData<F, C, D>,
)
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    InnerC: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
    InnerC::Hasher: AlgebraicHasher<F>,
{
    let (wire_information, common_data, prover_data, verifier_data) =
        reckle_std::binary_circuits::internal_circuit_setup::<F, C, InnerC, D>(
            inner_cd,
            prev_circuit_digest,
            min_degree_bits,
        );
    (
        InternalWireInformation {
            0: wire_information,
        },
        common_data,
        prover_data,
        verifier_data,
    )
}

pub fn compact_circuit_setup<F, C, InnerC, const D: usize>(
    inner_cd: &CommonCircuitData<F, D>,
    prev_circuit_digest: HashOut<F>,
    min_degree_bits: Option<&usize>,
) -> (
    CompactWireInformation<D>,
    CommonCircuitData<F, D>,
    ProverCircuitData<F, C, D>,
    VerifierCircuitData<F, C, D>,
)
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    InnerC: GenericConfig<D, F = F> + 'static,
    InnerC::Hasher: AlgebraicHasher<F>,
{
    let (wire_information, common_data, prover_data, verifier_data) =
        reckle_std::binary_circuits::compact_circuit_setup::<F, C, InnerC, D>(
            inner_cd,
            prev_circuit_digest,
            min_degree_bits,
        );
    (
        CompactWireInformation {
            0: wire_information,
        },
        common_data,
        prover_data,
        verifier_data,
    )
}
