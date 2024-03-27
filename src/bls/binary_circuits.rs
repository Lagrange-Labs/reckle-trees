use plonky2::field::extension::Extendable;
use plonky2::gates::noop::NoopGate;
use plonky2::hash::hash_types::{HashOut, HashOutTarget, RichField, NUM_HASH_OUT_ELTS};
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{
    CircuitConfig, CommonCircuitData, ProverCircuitData, VerifierCircuitData, VerifierCircuitTarget,
};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig};
use plonky2::plonk::proof::ProofWithPublicInputsTarget;

use plonky2_bn254::curves::g1curve_target::G1Target;

use crate::bls::wire_information::{
    CompactWireInformation, InternalWireInformation, LeafWireInformation,
};

use crate::utils::helpers::{
    conditional_equal_hash, conditional_equal_target, connect_targets, g1_is_zero,
};

use super::BN254_TO_U32_LIMBS;

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
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());

    let left_merkle_t = builder.add_virtual_hash();
    let right_merkle_t = builder.add_virtual_hash();
    let root_merkle_t = builder.hash_or_noop::<C::Hasher>(
        [
            left_merkle_t.elements.to_vec(),
            right_merkle_t.elements.to_vec(),
        ]
        .concat(),
    );

    let left_pk_u32 = builder.add_virtual_targets(BN254_TO_U32_LIMBS);
    let right_pk_u32 = builder.add_virtual_targets(BN254_TO_U32_LIMBS);

    let left_pk_t = G1Target::from_vec(&mut builder, &left_pk_u32);
    let right_pk_t = G1Target::from_vec(&mut builder, &right_pk_u32);
    let root_pk_t = left_pk_t.add(&mut builder, &right_pk_t);

    let left_hash_pk_t = builder.hash_or_noop::<C::Hasher>(left_pk_u32.to_vec());
    let right_hash_pk_t = builder.hash_or_noop::<C::Hasher>(right_pk_u32.to_vec());

    let left_pk_zero = g1_is_zero(&mut builder, &left_pk_t);
    let left_pk_non_zero = builder.not(left_pk_zero);
    let right_pk_zero = g1_is_zero(&mut builder, &right_pk_t);
    let right_pk_non_zero = builder.not(right_pk_zero);

    let one = builder.one();
    let zero = builder.zero();

    let left_cnt_t = builder.select(left_pk_non_zero, one, zero);
    let right_cnt_t = builder.select(right_pk_non_zero, one, zero);
    let root_cnt = builder.add(left_cnt_t, right_cnt_t);

    conditional_equal_hash(
        &mut builder,
        left_pk_non_zero,
        left_hash_pk_t,
        left_merkle_t,
    );
    conditional_equal_hash(
        &mut builder,
        right_pk_non_zero,
        right_hash_pk_t,
        right_merkle_t,
    );

    builder.register_public_inputs(&root_merkle_t.elements);
    builder.register_public_inputs(&root_pk_t.to_vec());
    builder.register_public_input(root_cnt);

    if let Some(min_degree_bits) = min_degree_bits {
        let min_gates = (1 << (min_degree_bits - 1)) + 1;
        for _ in builder.num_gates()..min_gates {
            builder.add_gate(NoopGate, vec![]);
        }
    }

    builder.print_gate_counts(0);
    let data = builder.build::<C>();

    let wire_information =
        LeafWireInformation::new(left_merkle_t, &left_pk_u32, right_merkle_t, &right_pk_u32);

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
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());

    let left_merkle_t = builder.add_virtual_hash();
    let right_merkle_t = builder.add_virtual_hash();
    let root_merkle_t = builder.hash_or_noop::<C::Hasher>(
        [
            left_merkle_t.elements.to_vec(),
            right_merkle_t.elements.to_vec(),
        ]
        .concat(),
    );

    let left_pk_u32 = builder.add_virtual_targets(BN254_TO_U32_LIMBS);
    let right_pk_u32 = builder.add_virtual_targets(BN254_TO_U32_LIMBS);

    let left_pk_t = G1Target::from_vec(&mut builder, &left_pk_u32);
    let right_pk_t = G1Target::from_vec(&mut builder, &right_pk_u32);
    let root_pk_t = left_pk_t.add(&mut builder, &right_pk_t);

    let left_cnt_t = builder.add_virtual_target();
    let right_cnt_t = builder.add_virtual_target();
    let root_cnt = builder.add(left_cnt_t, right_cnt_t);

    let left_pk_zero = g1_is_zero(&mut builder, &left_pk_t);
    let left_pk_non_zero = builder.not(left_pk_zero);
    let right_pk_zero = g1_is_zero(&mut builder, &right_pk_t);
    let right_pk_non_zero = builder.not(right_pk_zero);

    let prev_circuit_digest_target = builder.constant_hash(prev_circuit_digest);
    let verifier_circuit_target = VerifierCircuitTarget {
        constants_sigmas_cap: builder.add_virtual_cap(inner_cd.config.fri_config.cap_height),
        circuit_digest: prev_circuit_digest_target,
    };

    let zero = builder.zero();

    conditional_equal_target(&mut builder, left_cnt_t, zero, left_pk_zero);
    conditional_equal_target(&mut builder, right_cnt_t, zero, right_pk_zero);

    let (left_proof_target, right_proof_target) = verify_child_proof::<F, C, InnerC, D>(
        &mut builder,
        &verifier_circuit_target,
        inner_cd,
        left_pk_non_zero,
        &left_merkle_t,
        &left_pk_u32,
        &left_cnt_t,
        right_pk_non_zero,
        &right_merkle_t,
        &right_pk_u32,
        &right_cnt_t,
    );

    if let Some(min_degree_bits) = min_degree_bits {
        let min_gates = (1 << (min_degree_bits - 1)) + 1;
        for _ in builder.num_gates()..min_gates {
            builder.add_gate(NoopGate, vec![]);
        }
    }

    builder.register_public_inputs(&root_merkle_t.elements);
    builder.register_public_inputs(&root_pk_t.to_vec());
    builder.register_public_input(root_cnt);

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

    let root_merkle_t = builder.add_virtual_hash();
    let root_pk_u32 = builder.add_virtual_targets(BN254_TO_U32_LIMBS);
    let root_cnt = builder.add_virtual_target();

    let prev_circuit_digest_target = builder.constant_hash(prev_circuit_digest);

    builder.register_public_inputs(&root_merkle_t.elements);
    builder.register_public_inputs(&root_pk_u32.to_vec());
    builder.register_public_input(root_cnt);

    let verifier_circuit_target = VerifierCircuitTarget {
        constants_sigmas_cap: builder.add_virtual_cap(inner_cd.config.fri_config.cap_height),
        circuit_digest: prev_circuit_digest_target,
    };

    let proof_target = builder.add_virtual_proof_with_pis(inner_cd);
    connect_targets(
        &mut builder,
        &root_merkle_t.elements,
        &proof_target.public_inputs[0..NUM_HASH_OUT_ELTS],
    );
    connect_targets(
        &mut builder,
        &root_pk_u32,
        &proof_target.public_inputs[NUM_HASH_OUT_ELTS..20],
    );
    builder.connect(root_cnt, proof_target.public_inputs[20]);

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

fn verify_child_proof<F, C, InnerC, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    verifier_circuit_target: &VerifierCircuitTarget,
    inner_cd: &CommonCircuitData<F, D>,

    left_condition: BoolTarget,
    left_merkle_t: &HashOutTarget,
    left_pk_u32: &[Target],
    left_cnt_t: &Target,

    right_condition: BoolTarget,
    right_merkle_t: &HashOutTarget,
    right_pk_u32: &[Target],
    right_cnt_t: &Target,
) -> (
    ProofWithPublicInputsTarget<D>,
    ProofWithPublicInputsTarget<D>,
)
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    InnerC: GenericConfig<D, F = F> + 'static,
    InnerC::Hasher: AlgebraicHasher<F>,
    C::Hasher: AlgebraicHasher<F>,
{
    let left_proof_target = builder.add_virtual_proof_with_pis(inner_cd);
    connect_targets(
        builder,
        &left_merkle_t.elements,
        &left_proof_target.public_inputs[0..NUM_HASH_OUT_ELTS],
    );
    connect_targets(
        builder,
        &left_pk_u32,
        &left_proof_target.public_inputs[NUM_HASH_OUT_ELTS..20],
    );
    builder.connect(*left_cnt_t, left_proof_target.public_inputs[20]);

    let right_proof_target = builder.add_virtual_proof_with_pis(inner_cd);
    connect_targets(
        builder,
        &right_merkle_t.elements,
        &right_proof_target.public_inputs[0..NUM_HASH_OUT_ELTS],
    );
    connect_targets(
        builder,
        &right_pk_u32,
        &right_proof_target.public_inputs[NUM_HASH_OUT_ELTS..20],
    );
    builder.connect(*right_cnt_t, right_proof_target.public_inputs[20]);

    builder.conditionally_verify_proof::<InnerC>(
        left_condition,
        &left_proof_target,
        &verifier_circuit_target,
        &right_proof_target,
        &verifier_circuit_target,
        inner_cd,
    );
    builder.conditionally_verify_proof::<InnerC>(
        right_condition,
        &right_proof_target,
        &verifier_circuit_target,
        &left_proof_target,
        &verifier_circuit_target,
        inner_cd,
    );

    (left_proof_target, right_proof_target)
}
