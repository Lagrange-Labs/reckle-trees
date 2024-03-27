use std::collections::HashMap;

use itertools::Itertools;

use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::{HashOut, RichField};
use plonky2::iop::witness::PartialWitness;
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig};
use plonky2::plonk::proof::ProofWithPublicInputs;

use crate::bls::binary_pp::SNARK_PP;
use crate::bls::BN254_TO_U32_LIMBS;
use crate::utils::mt_binary::PartialMT;

pub struct PublicParamsAndInputs<const Q: usize, F, C, const D: usize>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F, Hash = HashOut<F>>,
    [(); 1 << Q]:,
{
    pub leaves: HashMap<u32, Vec<F>>,
    pub mt: PartialMT<F, C::Hasher>,
    pub pp: SNARK_PP<Q, F, C, D>,
}

pub struct LeafProver<'a, const Q: usize, F, C, const D: usize>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
    [(); 1 << Q]:,
{
    leaves: &'a HashMap<u32, Vec<F>>,
    mt: &'a PartialMT<F, C::Hasher>,
    pp: &'a SNARK_PP<Q, F, C, D>,
}

impl<'a, const Q: usize, F, C, const D: usize> LeafProver<'a, Q, F, C, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
    [(); 1 << Q]:,
{
    pub fn new(
        leaves: &'a HashMap<u32, Vec<F>>,
        pp: &'a SNARK_PP<Q, F, C, D>,
        mt: &'a PartialMT<F, C::Hasher>,
    ) -> LeafProver<'a, Q, F, C, D> {
        Self { leaves, mt, pp }
    }
    pub fn compute_pw(&mut self, bucket_index: u32) -> PartialWitness<F> {
        let g1_zero_u32 = (0..BN254_TO_U32_LIMBS)
            .into_iter()
            .map(|_| F::from_canonical_u32(0))
            .collect_vec();

        let key1 = (0, 2 * bucket_index);
        let key2 = (0, 2 * bucket_index + 1);

        let leaf_l = 2 * bucket_index;
        let leaf_r = 2 * bucket_index + 1;

        let left_pk = match (&self.leaves).get(&leaf_l) {
            Some(value) => value.clone(),
            None => g1_zero_u32.clone(),
        };

        let right_pk = match (&self.leaves).get(&leaf_r) {
            Some(value) => value.clone(),
            None => g1_zero_u32.clone(),
        };

        let left_merkle = (&self.mt.digests).get(&key1).unwrap().clone();
        let right_merkle = (&self.mt.digests).get(&key2).unwrap().clone();

        self.pp.leaf_wire_information.compute_pw(
            left_merkle,
            left_pk.as_slice(),
            right_merkle,
            right_pk.as_slice(),
        )
    }

    pub fn prove(&self, pw: PartialWitness<F>) -> anyhow::Result<ProofWithPublicInputs<F, C, D>> {
        let circuit_data = &self.pp.prover_leaf;
        circuit_data.prove(pw.clone())
    }
    pub fn from_public_params_and_inputs(data: &'a PublicParamsAndInputs<Q, F, C, D>) -> Self {
        Self {
            leaves: &data.leaves,
            mt: &data.mt,
            pp: &data.pp,
        }
    }
}

pub struct InternalProver<'a, const Q: usize, F, C, const D: usize>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
    [(); 1 << Q]:,
{
    mt: &'a PartialMT<F, C::Hasher>,
    pp: &'a SNARK_PP<Q, F, C, D>,
}

impl<'a, const Q: usize, F, C, const D: usize> InternalProver<'a, Q, F, C, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
    [(); 1 << Q]:,
{
    pub fn new(
        pp: &'a SNARK_PP<Q, F, C, D>,
        mt: &'a PartialMT<F, C::Hasher>,
    ) -> InternalProver<'a, Q, F, C, D> {
        Self { mt, pp }
    }

    pub fn compute_pw(
        &mut self,
        key: (u8, u32),
        left_proof: Option<ProofWithPublicInputs<F, C, D>>,
        right_proof: Option<ProofWithPublicInputs<F, C, D>>,
    ) -> PartialWitness<F>
    where
        C: GenericConfig<D, F = F> + 'static,
        C::Hasher: AlgebraicHasher<F>,
    {
        let g1_zero_and_cnt = (0..=BN254_TO_U32_LIMBS)
            .into_iter()
            .map(|_| F::from_canonical_u32(0))
            .collect_vec();

        let internal_config_index = key.0 as usize - (Q + 1);

        let index = key.1;
        let key1: (u8, u32) = (key.0 - 1, 2 * index);
        let key2: (u8, u32) = (key.0 - 1, 2 * index + 1);

        let left_merkle = self.mt.digests.get(&key1).unwrap().clone();
        let right_merkle = self.mt.digests.get(&key2).unwrap().clone();

        let actual_left_proof = match left_proof {
            Some(value) => value.clone(),
            None => {
                let cust_proof = ProofWithPublicInputs {
                    proof: right_proof.clone().unwrap().proof,
                    public_inputs: [left_merkle.elements.to_vec(), g1_zero_and_cnt.clone()]
                        .concat(),
                };
                cust_proof
            }
        };
        let actual_right_proof = match right_proof {
            Some(value) => value.clone(),

            None => {
                let cust_proof = ProofWithPublicInputs {
                    proof: actual_left_proof.proof.clone(),
                    public_inputs: [right_merkle.elements.to_vec(), g1_zero_and_cnt.clone()]
                        .concat(),
                };
                cust_proof
            }
        };

        let verifier_circuit_data_target_merkle_cap = if internal_config_index == 0 {
            self.pp
                .verifier_leaf
                .verifier_only
                .constants_sigmas_cap
                .clone()
        } else {
            self.pp.verifier_internal[internal_config_index - 1]
                .verifier_only
                .constants_sigmas_cap
                .clone()
        };

        self.pp.internal_wire_information[internal_config_index].compute_pw::<F, C>(
            actual_left_proof,
            actual_right_proof,
            verifier_circuit_data_target_merkle_cap.clone(),
        )
    }
    pub fn prove(
        &self,
        internal_config_index: usize,
        pw: PartialWitness<F>,
    ) -> anyhow::Result<ProofWithPublicInputs<F, C, D>> {
        self.pp.prover_internal[internal_config_index].prove(pw)
    }
    pub fn from_public_params_and_inputs(data: &'a PublicParamsAndInputs<Q, F, C, D>) -> Self {
        Self {
            mt: &data.mt,
            pp: &data.pp,
        }
    }
}

pub struct CompactProver<'a, const Q: usize, F, C, const D: usize>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
    [(); 1 << Q]:,
{
    pp: &'a SNARK_PP<Q, F, C, D>,
}

impl<'a, const Q: usize, F, C, const D: usize> CompactProver<'a, Q, F, C, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
    [(); 1 << Q]:,
{
    pub fn new(pp: &'a SNARK_PP<Q, F, C, D>) -> CompactProver<Q, F, C, D> {
        Self { pp }
    }

    pub fn compute_pw(
        &mut self,
        index: usize,
        proof: ProofWithPublicInputs<F, C, D>,
    ) -> PartialWitness<F> {
        let wire_information = &self.pp.wire_information_compact[index];

        let verifier_circuit_data_target_merkle_cap = if index == 0 {
            self.pp.verifier_internal[self.pp.log_max_capacity as usize - (Q + 1)]
                .verifier_only
                .constants_sigmas_cap
                .clone()
        } else {
            self.pp.verifier_compact[index - 1]
                .verifier_only
                .constants_sigmas_cap
                .clone()
        };
        wire_information.compute_pw::<F, C>(proof, verifier_circuit_data_target_merkle_cap.clone())
    }

    pub fn prove(
        &self,
        index: usize,
        pw: PartialWitness<F>,
    ) -> anyhow::Result<ProofWithPublicInputs<F, C, D>> {
        let circuit_data = &self.pp.prover_compact[index];
        circuit_data.prove(pw)
    }

    pub fn from_public_params_and_inputs(data: &'a PublicParamsAndInputs<Q, F, C, D>) -> Self {
        Self { pp: &data.pp }
    }
}
