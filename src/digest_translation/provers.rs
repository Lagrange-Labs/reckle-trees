use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::witness::PartialWitness;
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, GenericHashOut, Hasher};
use plonky2::plonk::proof::ProofWithPublicInputs;

use crate::digest_translation::binary_pp::SNARK_PP;
use crate::utils::helpers::u8_to_u32_le;
use crate::utils::mt_binary::PartialMT;

pub struct PublicParamsAndInputs<F, C, KH, PH, const D: usize>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
    KH: Hasher<F>,
    PH: AlgebraicHasher<F>,
{
    pub mt_kh: PartialMT<F, KH>,
    pub mt_ph: PartialMT<F, PH>,

    pub pp: SNARK_PP<F, C, D>,
}

pub struct LeafProver<'a, F, C, KH, PH, const D: usize>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
    KH: Hasher<F>,
    PH: AlgebraicHasher<F>,
{
    _mt_kh: &'a PartialMT<F, KH>,
    mt_ph: &'a PartialMT<F, PH>,
    pp: &'a SNARK_PP<F, C, D>,
}

impl<'a, F, C, KH, PH, const D: usize> LeafProver<'a, F, C, KH, PH, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
    KH: Hasher<F>,
    PH: AlgebraicHasher<F>,
{
    pub fn new(
        pp: &'a SNARK_PP<F, C, D>,
        mt_kh: &'a PartialMT<F, KH>,
        mt_ph: &'a PartialMT<F, PH>,
    ) -> Self {
        Self {
            _mt_kh: mt_kh,
            mt_ph,
            pp,
        }
    }

    pub fn compute_pw(&mut self, index: u32) -> PartialWitness<F> {
        let key1 = (0, 2 * index);
        let key2 = (0, 2 * index + 1);

        let left_data = (&self.mt_ph.digests).get(&key1).unwrap().clone();
        let right_data = (&self.mt_ph.digests).get(&key2).unwrap().clone();

        self.pp
            .leaf_wire_information
            .compute_pw(&left_data.elements, &right_data.elements)
    }

    pub fn prove(&self, pw: PartialWitness<F>) -> anyhow::Result<ProofWithPublicInputs<F, C, D>> {
        let circuit_data = &self.pp.prover_leaf;
        circuit_data.prove(pw.clone())
    }

    pub fn from_public_params_and_inputs(data: &'a PublicParamsAndInputs<F, C, KH, PH, D>) -> Self {
        Self {
            _mt_kh: &data.mt_kh,
            mt_ph: &data.mt_ph,
            pp: &data.pp,
        }
    }
}

pub struct InternalProver<'a, F, C, KH, PH, const D: usize>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
    KH: Hasher<F>,
    PH: AlgebraicHasher<F>,
{
    mt_kh: &'a PartialMT<F, KH>,
    mt_ph: &'a PartialMT<F, PH>,
    pp: &'a SNARK_PP<F, C, D>,
}

impl<'a, F, C, KH, PH, const D: usize> InternalProver<'a, F, C, KH, PH, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
    KH: Hasher<F>,
    PH: AlgebraicHasher<F>,
{
    pub fn new(
        pp: &'a SNARK_PP<F, C, D>,
        mt_kh: &'a PartialMT<F, KH>,
        mt_ph: &'a PartialMT<F, PH>,
    ) -> Self {
        Self { mt_kh, mt_ph, pp }
    }
    pub fn compute_pw(
        &mut self,
        key: (u8, u32),
        left_proof: Option<ProofWithPublicInputs<F, C, D>>,
        right_proof: Option<ProofWithPublicInputs<F, C, D>>,
    ) -> PartialWitness<F> {
        // start indexing into internal arrays at level 2
        let internal_config_index = (key.0 - 2) as usize;

        let index = key.1;

        let key1: (u8, u32) = (key.0 - 1, 2 * index);
        let key2: (u8, u32) = (key.0 - 1, 2 * index + 1);

        let left_kh = self.mt_kh.digests.get(&key1).unwrap().clone();
        let left_kh_vec = u8_to_u32_le(&KH::Hash::to_bytes(&left_kh))
            .iter()
            .map(|&x| F::from_canonical_u32(x))
            .collect::<Vec<_>>();

        let right_kh = self.mt_kh.digests.get(&key2).unwrap().clone();
        let right_kh_vec = u8_to_u32_le(&KH::Hash::to_bytes(&right_kh))
            .iter()
            .map(|&x| F::from_canonical_u32(x))
            .collect::<Vec<_>>();

        let left_ph = self.mt_ph.digests.get(&key1).unwrap().clone();
        let right_ph = self.mt_ph.digests.get(&key2).unwrap().clone();

        let left_proof_cust = ProofWithPublicInputs {
            proof: left_proof.clone().unwrap().proof,
            public_inputs: [left_ph.elements.to_vec(), left_kh_vec].concat(),
        };

        let right_proof_cust = ProofWithPublicInputs {
            proof: right_proof.clone().unwrap().proof,
            public_inputs: [right_ph.elements.to_vec(), right_kh_vec].concat(),
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
            left_proof_cust,
            right_proof_cust,
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
    pub fn from_public_params_and_inputs(data: &'a PublicParamsAndInputs<F, C, KH, PH, D>) -> Self {
        Self {
            mt_kh: &data.mt_kh,
            mt_ph: &data.mt_ph,
            pp: &data.pp,
        }
    }
}

pub struct CompactProver<'a, F, C, const D: usize>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
{
    pp: &'a SNARK_PP<F, C, D>,
}

impl<'a, F, C, const D: usize> CompactProver<'a, F, C, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
{
    pub fn new(pp: &'a SNARK_PP<F, C, D>) -> CompactProver<F, C, D> {
        Self { pp }
    }

    pub fn compute_pw(
        &mut self,
        index: usize,
        proof: ProofWithPublicInputs<F, C, D>,
    ) -> PartialWitness<F> {
        let wire_information = &self.pp.wire_information_compact[index];

        let verifier_circuit_data_target_merkle_cap = if index == 0 {
            self.pp.verifier_internal[self.pp.log_max_capacity as usize - 2]
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

    pub fn from_public_params_and_inputs<KH, PH>(
        data: &'a PublicParamsAndInputs<F, C, KH, PH, D>,
    ) -> Self
    where
        KH: Hasher<F>,
        PH: AlgebraicHasher<F>,
    {
        Self { pp: &data.pp }
    }
}
