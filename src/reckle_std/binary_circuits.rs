use plonky2::field::extension::Extendable;
use plonky2::gates::noop::NoopGate;
use plonky2::hash::hash_types::{HashOut, HashOutTarget, RichField, NUM_HASH_OUT_ELTS};
use plonky2::iop::target::BoolTarget;

use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::ProverCircuitData;
use plonky2::plonk::circuit_data::{CircuitConfig, CommonCircuitData};
use plonky2::plonk::circuit_data::{VerifierCircuitData, VerifierCircuitTarget};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig};
use plonky2::plonk::proof::ProofWithPublicInputsTarget;

use crate::reckle_std::wire_information::{
    CompactWireInformation, InternalWireInformation, LeafWireInformation,
};

use crate::utils::helpers::{
    compute_root_canonical, connect_inner_digests, connect_targets, is_hash_zero,
};

pub fn leaf_circuit_setup<F, C, const D: usize>(
    min_degree_bits: Option<&usize>,
) -> (
    LeafWireInformation<D>,
    CommonCircuitData<F, D>,
    ProverCircuitData<F, C, D>,
    VerifierCircuitData<F, C, D>,
)
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    C::Hasher: AlgebraicHasher<F>,
{
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());

    let left_merkle_target = builder.add_virtual_hash();
    let right_merkle_target = builder.add_virtual_hash();
    let root_merkle_target = builder.hash_or_noop::<C::Hasher>(
        [
            left_merkle_target.elements.to_vec(),
            right_merkle_target.elements.to_vec(),
        ]
        .concat(),
    );

    let left_canonical_target = builder.add_virtual_hash();
    let is_left_canonical_non_zero =
        connect_inner_digests::<F, D>(&mut builder, left_merkle_target, left_canonical_target);

    let right_canonical_target = builder.add_virtual_hash();
    let is_right_canonical_non_zero =
        connect_inner_digests::<F, D>(&mut builder, right_merkle_target, right_canonical_target);

    let selector = builder.and(is_left_canonical_non_zero, is_right_canonical_non_zero);

    let root_canonical_target = compute_root_canonical::<F, C, D>(
        &mut builder,
        selector,
        left_canonical_target,
        right_canonical_target,
    );

    builder.register_public_inputs(&root_merkle_target.elements);
    builder.register_public_inputs(&root_canonical_target.elements);

    if let Some(min_degree_bits) = min_degree_bits {
        let min_gates = (1 << (min_degree_bits - 1)) + 1;
        for _ in builder.num_gates()..min_gates {
            builder.add_gate(NoopGate, vec![]);
        }
    }

    builder.print_gate_counts(0);
    let data = builder.build::<C>();

    let wire_information = LeafWireInformation::new(
        left_merkle_target,
        left_canonical_target,
        right_merkle_target,
        right_canonical_target,
    );

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
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());

    let left_merkle_target = builder.add_virtual_hash();
    let right_merkle_target = builder.add_virtual_hash();
    let root_merkle_target = builder.hash_or_noop::<C::Hasher>(
        [
            left_merkle_target.elements.to_vec(),
            right_merkle_target.elements.to_vec(),
        ]
        .concat(),
    );

    let left_canonical_target = builder.add_virtual_hash();
    let is_left_canonical_zero = is_hash_zero(&mut builder, left_canonical_target);
    let is_left_canonical_non_zero = builder.not(is_left_canonical_zero);

    let right_canonical_target = builder.add_virtual_hash();
    let is_right_canonical_zero = is_hash_zero(&mut builder, right_canonical_target);
    let is_right_canonical_non_zero = builder.not(is_right_canonical_zero);

    let selector = builder.and(is_left_canonical_non_zero, is_right_canonical_non_zero);

    let root_canonical_target = compute_root_canonical::<F, C, D>(
        &mut builder,
        selector,
        left_canonical_target,
        right_canonical_target,
    );

    builder.register_public_inputs(&root_merkle_target.elements);
    builder.register_public_inputs(&root_canonical_target.elements);

    let prev_circuit_digest_target = builder.constant_hash(prev_circuit_digest);

    builder.print_gate_counts(0);

    let verifier_circuit_target = VerifierCircuitTarget {
        constants_sigmas_cap: builder.add_virtual_cap(inner_cd.config.fri_config.cap_height),
        circuit_digest: prev_circuit_digest_target,
    };

    let (left_proof_target, right_proof_target) =
        CircuitBuilderInnerProof::<F, C, InnerC, D>::verify_child_proof(
            &mut builder,
            &verifier_circuit_target,
            inner_cd,
            is_left_canonical_non_zero,
            &left_merkle_target,
            &left_canonical_target,
            is_right_canonical_non_zero,
            &right_merkle_target,
            &right_canonical_target,
        );

    if let Some(min_degree_bits) = min_degree_bits {
        let min_gates = (1 << (min_degree_bits - 1)) + 1;
        for _ in builder.num_gates()..min_gates {
            builder.add_gate(NoopGate, vec![]);
        }
    }

    builder.print_gate_counts(0);

    let data = builder.build::<C>();
    let common_data = data.verifier_data().common;
    let verifier_data = data.verifier_data();
    let prover_data = data.prover_data();

    let wire_information = InternalWireInformation::new(
        left_proof_target,
        right_proof_target,
        verifier_circuit_target.constants_sigmas_cap,
    );

    (wire_information, common_data, prover_data, verifier_data)
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
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());

    let merkle_target = builder.add_virtual_hash();
    let canonical_target = builder.add_virtual_hash();

    let prev_circuit_digest_target = builder.constant_hash(prev_circuit_digest);

    builder.register_public_inputs(&merkle_target.elements);
    builder.register_public_inputs(&canonical_target.elements);

    let verifier_circuit_target = VerifierCircuitTarget {
        constants_sigmas_cap: builder.add_virtual_cap(inner_cd.config.fri_config.cap_height),
        circuit_digest: prev_circuit_digest_target,
    };

    let proof_target = builder.add_virtual_proof_with_pis(inner_cd);
    connect_targets(
        &mut builder,
        &merkle_target.elements,
        &proof_target.public_inputs[0..NUM_HASH_OUT_ELTS],
    );
    connect_targets(
        &mut builder,
        &canonical_target.elements,
        &proof_target.public_inputs[NUM_HASH_OUT_ELTS..2 * NUM_HASH_OUT_ELTS],
    );

    builder.verify_proof::<InnerC>(&proof_target, &verifier_circuit_target, inner_cd);

    if let Some(min_degree_bits) = min_degree_bits {
        let min_gates = (1 << (min_degree_bits - 1)) + 1;
        for _ in builder.num_gates()..min_gates {
            builder.add_gate(NoopGate, vec![]);
        }
    }

    builder.print_gate_counts(0);
    let data = builder.build::<C>();

    let wire_information =
        CompactWireInformation::new(proof_target, verifier_circuit_target.constants_sigmas_cap);

    let common_data = data.verifier_data().common;
    let verifier_data = data.verifier_data();
    let prover_data = data.prover_data();

    (wire_information, common_data, prover_data, verifier_data)
}

pub trait CircuitBuilderInnerProof<F, C, InnerC, const D: usize>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    InnerC: GenericConfig<D, F = F> + 'static,
    InnerC::Hasher: AlgebraicHasher<F>,
    C::Hasher: AlgebraicHasher<F>,
{
    fn verify_child_proof(
        &mut self,
        verifier_circuit_target: &VerifierCircuitTarget,
        inner_cd: &CommonCircuitData<F, D>,

        left_condition: BoolTarget,
        left_merkle_target: &HashOutTarget,
        left_canonical_target: &HashOutTarget,

        right_condition: BoolTarget,
        right_merkle_target: &HashOutTarget,
        right_canonical_target: &HashOutTarget,
    ) -> (
        ProofWithPublicInputsTarget<D>,
        ProofWithPublicInputsTarget<D>,
    );
}
impl<F, C, InnerC, const D: usize> CircuitBuilderInnerProof<F, C, InnerC, D>
    for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    InnerC: GenericConfig<D, F = F> + 'static,
    InnerC::Hasher: AlgebraicHasher<F>,
    C::Hasher: AlgebraicHasher<F>,
{
    fn verify_child_proof(
        &mut self,

        verifier_circuit_target: &VerifierCircuitTarget,
        inner_cd: &CommonCircuitData<F, D>,

        left_condition: BoolTarget,
        left_merkle_target: &HashOutTarget,
        left_canonical_target: &HashOutTarget,

        right_condition: BoolTarget,
        right_merkle_target: &HashOutTarget,
        right_canonical_target: &HashOutTarget,
    ) -> (
        ProofWithPublicInputsTarget<D>,
        ProofWithPublicInputsTarget<D>,
    ) {
        let left_proof_target = self.add_virtual_proof_with_pis(inner_cd);
        connect_targets(
            self,
            &left_merkle_target.elements,
            &left_proof_target.public_inputs[0..NUM_HASH_OUT_ELTS],
        );
        connect_targets(
            self,
            &left_canonical_target.elements,
            &left_proof_target.public_inputs[NUM_HASH_OUT_ELTS..2 * NUM_HASH_OUT_ELTS],
        );

        let right_proof_target = self.add_virtual_proof_with_pis(inner_cd);
        connect_targets(
            self,
            &right_merkle_target.elements,
            &right_proof_target.public_inputs[0..NUM_HASH_OUT_ELTS],
        );
        connect_targets(
            self,
            &right_canonical_target.elements,
            &right_proof_target.public_inputs[NUM_HASH_OUT_ELTS..2 * NUM_HASH_OUT_ELTS],
        );

        self.conditionally_verify_proof::<InnerC>(
            left_condition,
            &left_proof_target,
            &verifier_circuit_target,
            &right_proof_target,
            &verifier_circuit_target,
            inner_cd,
        );
        self.conditionally_verify_proof::<InnerC>(
            right_condition,
            &right_proof_target,
            &verifier_circuit_target,
            &left_proof_target,
            &verifier_circuit_target,
            inner_cd,
        );

        (left_proof_target, right_proof_target)
    }
}
