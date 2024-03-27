use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::{HashOut, RichField, NUM_HASH_OUT_ELTS};
use plonky2::iop::target::Target;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{
    CircuitConfig, CommonCircuitData, ProverCircuitData, VerifierCircuitData, VerifierCircuitTarget,
};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, Hasher};
use plonky2::plonk::proof::ProofWithPublicInputsTarget;

use plonky2_crypto::biguint::{BigUintTarget, CircuitBuilderBiguint};
use plonky2_crypto::hash::keccak256::CircuitBuilderHashKeccak;

use crate::digest_translation::wire_information::{
    CompactWireInformation, InternalWireInformation, LeafWireInformation,
};
use crate::utils::helpers::{
    concate_keccak_input, connect_biguint_with_target, connect_targets,
    convert_target_to_u32target_le, range_check_bigint_limbs, BIGINT_LIMB_SIZE_BITS,
};

const INPUT_SIZE_BITS: usize = 256;

pub fn leaf_circuit_setup<F, C, KH, PH, const D: usize>() -> (
    LeafWireInformation<D>,
    CommonCircuitData<F, D>,
    ProverCircuitData<F, C, D>,
    VerifierCircuitData<F, C, D>,
)
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    KH: Hasher<F>,
    PH: AlgebraicHasher<F>,
    C::Hasher: AlgebraicHasher<F>,
{
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    let left_data_target: [Target; NUM_HASH_OUT_ELTS] = builder
        .add_virtual_targets(NUM_HASH_OUT_ELTS)
        .try_into()
        .unwrap();
    let right_data_target: [Target; NUM_HASH_OUT_ELTS] = builder
        .add_virtual_targets(NUM_HASH_OUT_ELTS)
        .try_into()
        .unwrap();
    let root_poseidon_target = builder
        .hash_or_noop::<PH>([left_data_target.to_vec(), right_data_target.to_vec()].concat())
        .elements;

    let left_data_u32target = convert_target_to_u32target_le(&mut builder, &left_data_target);
    let right_data_u32target = convert_target_to_u32target_le(&mut builder, &right_data_target);
    let left_data_bigint_target = BigUintTarget {
        limbs: left_data_u32target,
    };
    let right_data_bigint_target = BigUintTarget {
        limbs: right_data_u32target,
    };
    let concat_left_right = concate_keccak_input(
        &mut builder,
        INPUT_SIZE_BITS,
        left_data_bigint_target,
        right_data_bigint_target,
    );
    let root_keccak_target = builder.hash_keccak256(&concat_left_right);

    builder.register_public_inputs(&root_poseidon_target);
    for i in 0..root_keccak_target.num_limbs() {
        builder.register_public_input(root_keccak_target.limbs[i].0);
    }

    builder.print_gate_counts(0);
    let data = builder.build::<C>();

    let wire_information = LeafWireInformation::<D>::new(left_data_target, right_data_target);

    let common_data = data.verifier_data().common;
    let verifier_data = data.verifier_data();
    let prover_data = data.prover_data();

    (wire_information, common_data, prover_data, verifier_data)
}

pub fn internal_circuit_setup<F, C, InnerC, KH, PH, const D: usize>(
    inner_cd: &CommonCircuitData<F, D>,
    prev_circuit_digest: PH::Hash,
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
    KH: Hasher<F>,
    PH: AlgebraicHasher<F>,
    C::Hasher: AlgebraicHasher<F>,
    InnerC::Hasher: AlgebraicHasher<F>,
{
    let input_limb_size = INPUT_SIZE_BITS / BIGINT_LIMB_SIZE_BITS;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());

    let prev_circuit_digest_target = builder.constant_hash(prev_circuit_digest);
    let verifier_circuit_target = VerifierCircuitTarget {
        constants_sigmas_cap: builder.add_virtual_cap(inner_cd.config.fri_config.cap_height),
        circuit_digest: prev_circuit_digest_target,
    };

    let left_poseidon_target: [Target; NUM_HASH_OUT_ELTS] = builder
        .add_virtual_targets(NUM_HASH_OUT_ELTS)
        .try_into()
        .unwrap();
    let right_poseidon_target: [Target; NUM_HASH_OUT_ELTS] = builder
        .add_virtual_targets(NUM_HASH_OUT_ELTS)
        .try_into()
        .unwrap();

    let root_poseidon_target = builder
        .hash_or_noop::<PH>(
            [
                left_poseidon_target.to_vec(),
                right_poseidon_target.to_vec(),
            ]
            .concat(),
        )
        .elements;

    let left_keccak_target = builder.add_virtual_biguint_target(input_limb_size);
    let right_keccak_target = builder.add_virtual_biguint_target(input_limb_size);

    range_check_bigint_limbs(&mut builder, &left_keccak_target, 32);
    range_check_bigint_limbs(&mut builder, &right_keccak_target, 32);
    let concat_left_right = concate_keccak_input(
        &mut builder,
        INPUT_SIZE_BITS,
        left_keccak_target.clone(),
        right_keccak_target.clone(),
    );

    let root_keccak_target = builder.hash_keccak256(&concat_left_right);

    let (left_proof_target, right_proof_target) = verify_child_proof::<F, C, InnerC, KH, PH, D>(
        &mut builder,
        &verifier_circuit_target,
        inner_cd,
        left_poseidon_target,
        right_poseidon_target,
        left_keccak_target.clone(),
        right_keccak_target.clone(),
    );

    builder.register_public_inputs(&root_poseidon_target);
    for i in 0..root_keccak_target.num_limbs() {
        builder.register_public_input(root_keccak_target.limbs[i].0);
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
) -> (
    CompactWireInformation<D>,
    CommonCircuitData<F, D>,
    ProverCircuitData<F, C, D>,
    VerifierCircuitData<F, C, D>,
)
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    C::Hasher: AlgebraicHasher<F>,
    InnerC: GenericConfig<D, F = F> + 'static,
    InnerC::Hasher: AlgebraicHasher<F>,
{
    let input_limb_size = INPUT_SIZE_BITS / BIGINT_LIMB_SIZE_BITS;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());

    let prev_circuit_digest_target = builder.constant_hash(prev_circuit_digest);
    let verifier_circuit_target = VerifierCircuitTarget {
        constants_sigmas_cap: builder.add_virtual_cap(inner_cd.config.fri_config.cap_height),
        circuit_digest: prev_circuit_digest_target,
    };

    let root_poseidon_target: [Target; NUM_HASH_OUT_ELTS] = builder
        .add_virtual_targets(NUM_HASH_OUT_ELTS)
        .try_into()
        .unwrap();

    let root_keccak_target = builder.add_virtual_biguint_target(input_limb_size);

    let proof_target = builder.add_virtual_proof_with_pis(inner_cd);

    connect_targets(
        &mut builder,
        &root_poseidon_target,
        &proof_target.public_inputs[0..NUM_HASH_OUT_ELTS],
    );
    connect_biguint_with_target(
        &mut builder,
        &root_keccak_target,
        &proof_target.public_inputs[NUM_HASH_OUT_ELTS..12],
    );

    builder.verify_proof::<InnerC>(&proof_target, &verifier_circuit_target, inner_cd);

    builder.register_public_inputs(&root_poseidon_target);
    for i in 0..root_keccak_target.num_limbs() {
        builder.register_public_input(root_keccak_target.limbs[i].0);
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

pub fn verify_child_proof<F, C, InnerC, KH, PH, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,

    verifier_circuit_target: &VerifierCircuitTarget,
    inner_cd: &CommonCircuitData<F, D>,

    left_poseidon_target: [Target; NUM_HASH_OUT_ELTS],
    right_poseidon_target: [Target; NUM_HASH_OUT_ELTS],

    left_keccak_target: BigUintTarget,
    right_keccak_target: BigUintTarget,
) -> (
    ProofWithPublicInputsTarget<D>,
    ProofWithPublicInputsTarget<D>,
)
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    InnerC: GenericConfig<D, F = F> + 'static,
    KH: Hasher<F>,
    PH: AlgebraicHasher<F>,
    C::Hasher: AlgebraicHasher<F>,
    InnerC::Hasher: AlgebraicHasher<F>,
{
    let left_proof_target = builder.add_virtual_proof_with_pis(inner_cd);
    let right_proof_target = builder.add_virtual_proof_with_pis(inner_cd);

    connect_targets(
        builder,
        &left_poseidon_target,
        &left_proof_target.public_inputs[0..NUM_HASH_OUT_ELTS],
    );
    connect_targets(
        builder,
        &right_poseidon_target,
        &right_proof_target.public_inputs[0..NUM_HASH_OUT_ELTS],
    );

    connect_biguint_with_target(
        builder,
        &left_keccak_target,
        &left_proof_target.public_inputs[NUM_HASH_OUT_ELTS..12],
    );
    connect_biguint_with_target(
        builder,
        &right_keccak_target,
        &right_proof_target.public_inputs[NUM_HASH_OUT_ELTS..12],
    );

    builder.verify_proof::<InnerC>(&left_proof_target, &verifier_circuit_target, inner_cd);
    builder.verify_proof::<InnerC>(&right_proof_target, &verifier_circuit_target, inner_cd);

    (left_proof_target, right_proof_target)
}
