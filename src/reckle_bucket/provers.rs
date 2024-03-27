use itertools::Itertools;

use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::{HashOut, RichField};
use plonky2::iop::witness::PartialWitness;
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig};
use plonky2::plonk::proof::ProofWithPublicInputs;

use crate::reckle_bucket::binary_pp::SNARK_PP;
use crate::utils::canonical::CanonicalTree;
use crate::utils::mt_binary::PartialMT;

pub struct PublicParamsAndInputs<const Q: usize, F, C, const D: usize>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F, Hash = HashOut<F>>,
    [(); 1 << Q]:,
{
    pub mt: PartialMT<F, C::Hasher>,
    pub ct: CanonicalTree<F, C::Hasher>,
    pub pp: SNARK_PP<Q, F, C, D>,
}

pub struct LeafProver<'a, const Q: usize, F, C, const D: usize>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
    [(); 1 << Q]:,
{
    mt: &'a PartialMT<F, C::Hasher>,
    ct: &'a CanonicalTree<F, C::Hasher>,
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
        pp: &'a SNARK_PP<Q, F, C, D>,
        mt: &'a PartialMT<F, C::Hasher>,
        ct: &'a CanonicalTree<F, C::Hasher>,
    ) -> LeafProver<'a, Q, F, C, D> {
        Self { mt, ct, pp }
    }

    pub fn compute_pw(&mut self, bucket_index: u32) -> PartialWitness<F> {
        let bucket_size = 1 << Q as u32;
        let start_index = bucket_size * bucket_index;
        let end_index = bucket_size * (bucket_index + 1);

        let merkle_targets_q = (start_index..end_index)
            .into_iter()
            .map(|i| {
                let key = (0 as u8, i);
                (&self.mt.digests).get(&key).unwrap().clone()
            })
            .collect_vec();

        let canonical_targets_q = (start_index..end_index)
            .into_iter()
            .map(|i| {
                let key = (0 as u8, i);
                match (&self.ct.digests).get(&key) {
                    Some(value) => value.clone(),
                    None => CanonicalTree::<F, C::Hasher>::default(),
                }
            })
            .collect_vec();

        self.pp
            .leaf_wire_information
            .compute_pw(&merkle_targets_q, &canonical_targets_q)
    }

    pub fn prove(&self, pw: PartialWitness<F>) -> anyhow::Result<ProofWithPublicInputs<F, C, D>> {
        let circuit_data = &self.pp.prover_leaf;
        circuit_data.prove(pw.clone())
    }
    pub fn from_public_params_and_inputs(data: &'a PublicParamsAndInputs<Q, F, C, D>) -> Self {
        Self {
            mt: &data.mt,
            ct: &data.ct,
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
    ct: &'a CanonicalTree<F, C::Hasher>,
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
        ct: &'a CanonicalTree<F, C::Hasher>,
    ) -> InternalProver<'a, Q, F, C, D> {
        Self { mt, ct, pp }
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
        // start indexing into internal arrays at level 2
        let internal_config_index = key.0 as usize - (Q + 1);

        let index = key.1;
        let key1: (u8, u32) = (key.0 - 1, 2 * index);
        let key2: (u8, u32) = (key.0 - 1, 2 * index + 1);

        let left_merkle = self.mt.digests.get(&key1).unwrap().clone();
        let right_merkle = self.mt.digests.get(&key2).unwrap().clone();

        let left_canonical = match self.ct.digests.get(&key1) {
            Some(value) => value.clone(),
            None => CanonicalTree::<F, C::Hasher>::default(),
        };
        let right_canonical = match self.ct.digests.get(&key2) {
            Some(value) => value.clone(),
            None => CanonicalTree::<F, C::Hasher>::default(),
        };

        let actual_left_proof = match left_proof {
            Some(value) => value.clone(),
            None => {
                let cust_proof = ProofWithPublicInputs {
                    proof: right_proof.clone().unwrap().proof,
                    public_inputs: [left_merkle.elements, left_canonical.elements].concat(),
                };
                cust_proof
            }
        };
        let actual_right_proof = match right_proof {
            Some(value) => value.clone(),

            None => {
                let cust_proof = ProofWithPublicInputs {
                    proof: actual_left_proof.proof.clone(),
                    public_inputs: [right_merkle.elements, right_canonical.elements].concat(),
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

        self.pp.internal_wire_information[internal_config_index]
            .0
            .compute_pw::<F, C>(
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
            ct: &data.ct,
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
        wire_information
            .0
            .compute_pw::<F, C>(proof, verifier_circuit_data_target_merkle_cap.clone())
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
