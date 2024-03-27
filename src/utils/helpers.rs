use ark_bn254::G1Affine;
use ark_std::UniformRand;
use num::BigUint;

use plonky2::{
    field::{extension::Extendable, types::Field},
    hash::hash_types::{HashOutTarget, RichField, NUM_HASH_OUT_ELTS},
    iop::target::{BoolTarget, Target},
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CommonCircuitData, ProverCircuitData, VerifierCircuitData},
        config::{AlgebraicHasher, GenericConfig},
    },
};

use itertools::Itertools;
use plonky2_bn254::curves::{
    g1curve_target::G1Target, BN254GateSerializer, BN254GeneratorSerializer,
};
use plonky2_crypto::{
    biguint::{BigUintTarget, CircuitBuilderBiguint},
    hash::{keccak256::KECCAK256_R, HashInputTarget},
    u32::arithmetic_u32::{CircuitBuilderU32, U32Target},
};
use rand::rngs::StdRng;
use rand::Rng;
use std::{
    collections::{HashMap, HashSet},
    marker::PhantomData,
};

use crate::bls::BN254_TO_U32_LIMBS;

pub fn generate_recproofs_leaves<F>(
    leaf_size_including_index: usize,
    r: &mut StdRng,
    subset_indices: &HashSet<u32>,
) -> HashMap<u32, Vec<F>>
where
    F: Field,
{
    assert!(leaf_size_including_index > 1);
    let leaves: HashMap<u32, Vec<F>> = subset_indices
        .clone()
        .into_iter()
        .sorted()
        .map(|i| {
            let data = (0..leaf_size_including_index - 1)
                .map(|_| F::from_canonical_u64(r.gen()))
                .collect::<Vec<_>>();
            let value = [[F::from_canonical_u64(i as u64)].to_vec(), data].concat();
            (i as u32, value)
        })
        .collect::<HashMap<_, _>>();
    leaves
}

pub fn generate_leaf_value<F>(
    leaf_size_including_index: usize,
    r: &mut StdRng,
    index: u32,
) -> Vec<F>
where
    F: Field,
{
    assert!(leaf_size_including_index > 1);
    let data = (0..leaf_size_including_index - 1)
        .map(|_| F::from_canonical_u64(r.gen()))
        .collect::<Vec<_>>();
    let value = [[F::from_canonical_u64(index as u64)].to_vec(), data].concat();
    value
}

pub(crate) fn hash_select<F, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    selector: BoolTarget,
    left_target: HashOutTarget,
    right_target: HashOutTarget,
) -> HashOutTarget
where
    F: RichField + Extendable<D>,
{
    assert!(NUM_HASH_OUT_ELTS == left_target.elements.len());
    assert!(NUM_HASH_OUT_ELTS == right_target.elements.len());
    let hash_as_vec = (0..NUM_HASH_OUT_ELTS)
        .into_iter()
        .map(|i| builder.select(selector, left_target.elements[i], right_target.elements[i]))
        .collect_vec();

    HashOutTarget::from_vec(hash_as_vec)
}

pub(crate) fn compute_root_canonical<F, C, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    selector: BoolTarget,
    left_canonical_target: HashOutTarget,
    right_canonical_target: HashOutTarget,
) -> HashOutTarget
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    C::Hasher: AlgebraicHasher<F>,
{
    assert!(NUM_HASH_OUT_ELTS == left_canonical_target.elements.len());
    assert!(NUM_HASH_OUT_ELTS == right_canonical_target.elements.len());

    let concat_hash = builder.hash_or_noop::<C::Hasher>(
        [
            left_canonical_target.elements.to_vec(),
            right_canonical_target.elements.to_vec(),
        ]
        .concat(),
    );

    let add_hash = HashOutTarget::from_vec(
        (0..NUM_HASH_OUT_ELTS)
            .into_iter()
            .map(|i| {
                builder.add(
                    left_canonical_target.elements[i],
                    right_canonical_target.elements[i],
                )
            })
            .collect_vec(),
    );
    let root_canonical_target = hash_select(builder, selector, concat_hash, add_hash);

    root_canonical_target
}

pub(crate) fn conditional_equal_hash<F, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    selector: BoolTarget,
    left_target: HashOutTarget,
    right_target: HashOutTarget,
) where
    F: RichField + Extendable<D>,
{
    assert!(NUM_HASH_OUT_ELTS == left_target.elements.len());
    assert!(NUM_HASH_OUT_ELTS == right_target.elements.len());

    for i in 0..NUM_HASH_OUT_ELTS {
        let left = builder.mul(left_target.elements[i], selector.target);
        let right = builder.mul(right_target.elements[i], selector.target);
        builder.connect(left, right);
    }
}

pub(crate) fn is_hash_zero<F, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    input_target: HashOutTarget,
) -> BoolTarget
where
    F: RichField + Extendable<D>,
{
    let zero = builder.zero();
    let mut result_bool = builder.constant_bool(true);
    for i in 0..NUM_HASH_OUT_ELTS {
        let is_zero = builder.is_equal(input_target.elements[i], zero);
        result_bool = builder.and(is_zero, result_bool);
    }
    result_bool
}

pub(crate) fn connect_inner_digests<F, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    merkle_target: HashOutTarget,
    canonical_target: HashOutTarget,
) -> BoolTarget
where
    F: RichField + Extendable<D>,
{
    let is_canonical_zero = is_hash_zero(builder, canonical_target);
    let is_canonical_non_zero = builder.not(is_canonical_zero);
    conditional_equal_hash(
        builder,
        is_canonical_non_zero,
        canonical_target,
        merkle_target,
    );
    is_canonical_non_zero
}

pub(crate) fn connect_targets<F, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    left_target: &[Target],
    right_target: &[Target],
) where
    F: RichField + Extendable<D>,
{
    assert!(left_target.len() == right_target.len());
    for i in 0..left_target.len() {
        builder.connect(left_target[i], right_target[i]);
    }
}

// Digest translation ==========================================================
pub const BIGINT_LIMB_SIZE_BITS: usize = 32;

pub fn connect_biguint_with_target<F, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    lhs: &BigUintTarget,
    rhs: &[Target],
) where
    F: RichField + Extendable<D>,
{
    let rhs = rhs.iter().map(|&a| U32Target(a)).collect::<Vec<_>>();
    let min_limbs = lhs.num_limbs().min(rhs.len());
    for i in 0..min_limbs {
        builder.connect_u32(lhs.get_limb(i), rhs[i]);
    }
}

pub fn concate_keccak_input<F, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    input_size_bits: usize,
    left_data_bigint_target: BigUintTarget,
    right_data_bigint_target: BigUintTarget,
) -> HashInputTarget
where
    F: RichField + Extendable<D>,
{
    // Keccak block = 1088 bits
    // Say input = 512 bits
    // Keccak block = [input | 10...01]
    let keccak_block_limb_size = KECCAK256_R / BIGINT_LIMB_SIZE_BITS;
    let data_padding_len: usize = (KECCAK256_R - 2 * input_size_bits) / 32;
    let input_limb_size = input_size_bits / BIGINT_LIMB_SIZE_BITS;
    let pad_zero_start = 2 * input_limb_size + 1;

    let concat_bigint_target = builder.add_virtual_biguint_target(keccak_block_limb_size);
    let start_pad = builder.constant_u32(0x00000001);
    let end_pad = builder.constant_u32(0x80000000);

    let zero_vec_u32 = (0..data_padding_len - 2)
        .map(|_| builder.constant_u32(0))
        .collect::<Vec<_>>();

    for i in 0..input_limb_size {
        builder.connect_u32(
            left_data_bigint_target.get_limb(i),
            concat_bigint_target.get_limb(i),
        );
        builder.connect_u32(
            right_data_bigint_target.get_limb(i),
            concat_bigint_target.get_limb(i + input_limb_size),
        );
    }

    builder.connect_u32(
        start_pad,
        concat_bigint_target.get_limb(2 * input_limb_size),
    );

    builder.connect_u32(
        end_pad,
        concat_bigint_target.get_limb(keccak_block_limb_size - 1),
    );

    for i in pad_zero_start..keccak_block_limb_size - 1 {
        builder.connect_u32(
            zero_vec_u32[i - pad_zero_start],
            concat_bigint_target.get_limb(i),
        );
    }

    // Works only when the concatenate input is less 1088 bits
    let concat_left_right = HashInputTarget {
        input: concat_bigint_target.clone(),
        input_bits: KECCAK256_R,
        blocks: Vec::new(),
    };

    concat_left_right
}

pub fn convert_target_to_u32target_le<F, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    data: &[Target],
) -> Vec<U32Target>
where
    F: RichField + Extendable<D>,
{
    let data_vec = data
        .into_iter()
        .map(|a| builder.split_low_high(*a, 32, 64))
        .flat_map(|tup| [tup.0, tup.1])
        .map(U32Target)
        .collect::<Vec<_>>();
    data_vec
}

pub fn range_check_bigint_limbs<F, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    values: &BigUintTarget,
    n_log: usize,
) where
    F: RichField + Extendable<D>,
{
    values
        .limbs
        .iter()
        .map(|x| builder.range_check(x.0, n_log))
        .collect_vec();
}

pub fn u8_to_u32_le(data: &Vec<u8>) -> Vec<u32> {
    let result = data
        .chunks(4)
        .into_iter()
        .map(|x| u32::from_le_bytes(x[0..4].try_into().unwrap()))
        .collect::<Vec<_>>();
    result
}

// BLS =========================================================================
pub(crate) fn conditional_equal_target<F, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    x: Target,
    y: Target,
    selector: BoolTarget,
) where
    F: RichField + Extendable<D>,
{
    let check_x = builder.mul(x, selector.target);
    let check_y = builder.mul(y, selector.target);
    builder.connect(check_x, check_y);
}

pub(crate) fn g1_is_zero<F, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    input: &G1Target<F, D>,
) -> BoolTarget
where
    F: RichField + Extendable<D>,
{
    let x_b = input.x.is_zero(builder);
    let y_b = input.y.is_zero(builder);
    builder.and(x_b, y_b)
}
pub fn generate_bls_pk<F>(r: &mut StdRng) -> Vec<F>
where
    F: Field,
{
    let pk = G1Affine::rand(r);
    g1_affine_to_field::<F>(pk)
}
pub fn g1_affine_to_field<F>(data: G1Affine) -> Vec<F>
where
    F: Field,
{
    g1_affine_to_u32(data)
        .into_iter()
        .map(|x| F::from_canonical_u32(x))
        .collect_vec()
}
pub fn g1_affine_to_u32(data: G1Affine) -> Vec<u32> {
    let x_big: BigUint = data.x.into();
    let y_big: BigUint = data.y.into();

    let mut x_u32 = x_big.to_u32_digits();
    let mut y_u32 = y_big.to_u32_digits();

    x_u32.extend(vec![0; BN254_TO_U32_LIMBS / 2 - x_u32.len()]);
    y_u32.extend(vec![0; BN254_TO_U32_LIMBS / 2 - y_u32.len()]);

    [x_u32, y_u32].concat()
}
pub fn generate_bls_pks<F>(r: &mut StdRng, subset_indices: &HashSet<u32>) -> HashMap<u32, Vec<F>>
where
    F: Field,
{
    let leaves: HashMap<u32, Vec<F>> = subset_indices
        .clone()
        .into_iter()
        .sorted()
        .map(|i| {
            let value = generate_bls_pk::<F>(r);
            (i as u32, value)
        })
        .collect::<HashMap<_, _>>();
    leaves
}

// Baseline ====================================================================
pub fn convert_hashout_to_biguint<F, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    input: &HashOutTarget,
) -> BigUintTarget
where
    F: RichField + Extendable<D>,
{
    let wires_target = input.elements;
    let wires_u32target = convert_target_to_u32target_le(builder, &wires_target);
    BigUintTarget {
        limbs: wires_u32target,
    }
}

pub fn get_pp_size_std<F, C, const D: usize>(
    cd: CommonCircuitData<F, D>,
    pd: &ProverCircuitData<F, C, D>,
    vd: VerifierCircuitData<F, C, D>,
) where
    C: GenericConfig<D, F = F> + 'static,
    F: RichField + Extendable<D>,
    C::Hasher: AlgebraicHasher<F>,
{
    let factor_1024 = 1024.0;
    let gate_serializer = plonky2_crypto::u32::gates::HashGateSerializer;
    let gen_serializer = plonky2_crypto::u32::gates::HashGeneratorSerializer {
        _phantom: std::marker::PhantomData::<C>,
    };

    let cd_size = cd.to_bytes(&gate_serializer).unwrap().len() as f64 / factor_1024;
    let pd_size = pd
        .to_bytes(&gate_serializer, &gen_serializer)
        .unwrap()
        .len() as f64
        / factor_1024
        / factor_1024;
    let vd_size = vd.to_bytes(&gate_serializer).unwrap().len() as f64 / factor_1024;

    println!(
        "=== Public parameters: common data: {:>4.2} KiB, prover data: {:>6.2} MiB, verifier data: {:>4.2} KiB",
        cd_size, pd_size, vd_size
    );
}

pub fn get_pp_size_ecc<F, C, const D: usize>(
    cd: CommonCircuitData<F, D>,
    pd: &ProverCircuitData<F, C, D>,
    vd: VerifierCircuitData<F, C, D>,
) where
    C: GenericConfig<D, F = F> + 'static,
    F: RichField + Extendable<D>,
    C::Hasher: AlgebraicHasher<F>,
{
    let factor_1024 = 1024.0;
    let gate_serializer = BN254GateSerializer {};
    let gen_serializer = BN254GeneratorSerializer::<C, D> {
        _phantom: PhantomData,
    };

    let cd_size = cd.to_bytes(&gate_serializer).unwrap().len() as f64 / factor_1024;
    let pd_size = pd
        .to_bytes(&gate_serializer, &gen_serializer)
        .unwrap()
        .len() as f64
        / factor_1024
        / factor_1024;
    let vd_size = vd.to_bytes(&gate_serializer).unwrap().len() as f64 / factor_1024;

    println!(
        "=== Public parameters: common data: {:>4.2} KiB, prover data: {:>6.2} MiB, verifier data: {:>4.2} KiB",
        cd_size, pd_size, vd_size
    );
}

pub(crate) fn merkle_select<F, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    selector: BoolTarget,
    first_input: HashOutTarget,
    second_input: HashOutTarget,
) -> (HashOutTarget, HashOutTarget)
where
    F: RichField + Extendable<D>,
{
    let not_selector = builder.not(selector);

    let left = hash_select(builder, selector, first_input, second_input);
    let right = hash_select(builder, not_selector, first_input, second_input);
    (left, right)
}
