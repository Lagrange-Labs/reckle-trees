use crate::reckle_std::binary_pp::SNARK_PP;
use crate::utils::canonical::CanonicalTree;
use crate::utils::mt_binary::PartialMT;

use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::{HashOut, RichField};
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::witness::PartialWitness;
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, Hasher, PoseidonGoldilocksConfig};
use plonky2::plonk::proof::ProofWithPublicInputs;

pub const DEF_D: usize = 2;

pub type DefC = PoseidonGoldilocksConfig;

pub type DefF = <DefC as GenericConfig<DEF_D>>::F;

pub type DefH = PoseidonHash;

pub struct PublicParamsAndInputs {
    pub mt: PartialMT<DefF, DefH>,
    pub ct: CanonicalTree<DefF, DefH>,
    pub pp: SNARK_PP<DefF, DefC, DEF_D>,
}

pub struct LeafProver<'a, F, H, C, const D: usize>
    where
        F: RichField + Extendable<D>,
        H: Hasher<F>,
        C: GenericConfig<D, F=F> + 'static,
        C::Hasher: AlgebraicHasher<F>,
{
    mt: &'a PartialMT<F, H>,
    ct: &'a CanonicalTree<F, H>,
    pp: &'a SNARK_PP<F, C, D>,
}

impl<'a, F, H, C, const D: usize> LeafProver<'a, F, H, C, D>
    where
        F: RichField + Extendable<D>,
        H: AlgebraicHasher<F>,
        C: GenericConfig<D, F=F> + 'static,
        C::Hasher: AlgebraicHasher<F>,
{
    pub fn new(
        pp: &'a SNARK_PP<F, C, D>,
        mt: &'a PartialMT<F, H>,
        ct: &'a CanonicalTree<F, H>,
    ) -> LeafProver<'a, F, H, C, D> {
        Self { mt, ct, pp }
    }

    pub fn compute_pw(&mut self, index: u32) -> PartialWitness<F> {
        let key1 = (0, 2 * index);
        let key2 = (0, 2 * index + 1);

        let left_canonical: HashOut<F> = match (&self.ct.digests).get(&key1) {
            Some(value) => value.clone(),
            None => CanonicalTree::<F, H>::default(),
        };
        let right_canonical = match (&self.ct.digests).get(&key2) {
            Some(value) => value.clone(),
            None => CanonicalTree::<F, H>::default(),
        };

        let left_merkle = (&self.mt.digests).get(&key1).unwrap().clone();
        let right_merkle = (&self.mt.digests).get(&key2).unwrap().clone();

        self.pp.leaf_wire_information.compute_pw(
            left_merkle,
            left_canonical,
            right_merkle,
            right_canonical,
        )
    }

    pub fn prove(&self, pw: PartialWitness<F>) -> anyhow::Result<ProofWithPublicInputs<F, C, D>> {
        let circuit_data = &self.pp.prover_leaf;
        circuit_data.prove(pw.clone())
    }
}

impl<'a> LeafProver<'a, DefF, DefH, DefC, 2> {
    pub fn from_public_params_and_inputs(data: &'a PublicParamsAndInputs) -> Self {
        Self {
            mt: &data.mt,
            ct: &data.ct,
            pp: &data.pp,
        }
    }
}

pub struct InternalProver<'a, F, H, C, const D: usize>
    where
        F: RichField + Extendable<D>,
        H: Hasher<F>,
        C: GenericConfig<D, F=F> + 'static,
        C::Hasher: AlgebraicHasher<F>,
{
    mt: &'a PartialMT<F, H>,
    ct: &'a CanonicalTree<F, H>,
    pp: &'a SNARK_PP<F, C, D>,
}

impl<'a, F, H, C, const D: usize> InternalProver<'a, F, H, C, D>
    where
        F: RichField + Extendable<D>,
        H: AlgebraicHasher<F>,
        C: GenericConfig<D, F=F> + 'static,
        C::Hasher: AlgebraicHasher<F>,
{
    pub fn new(
        pp: &'a SNARK_PP<F, C, D>,
        mt: &'a PartialMT<F, H>,
        ct: &'a CanonicalTree<F, H>,
    ) -> InternalProver<'a, F, H, C, D> {
        Self { mt, ct, pp }
    }

    pub fn compute_pw(
        &mut self,
        key: (u8, u32),
        left_proof: Option<ProofWithPublicInputs<F, C, D>>,
        right_proof: Option<ProofWithPublicInputs<F, C, D>>,
    ) -> PartialWitness<F>
        where
            C: GenericConfig<D, F=F> + 'static,
            C::Hasher: AlgebraicHasher<F>,
    {
        // start indexing into internal arrays at level 2
        let internal_config_index = (key.0 - 2) as usize;

        let index = key.1;
        let key1: (u8, u32) = (key.0 - 1, 2 * index);
        let key2: (u8, u32) = (key.0 - 1, 2 * index + 1);

        let left_merkle = self.mt.digests.get(&key1).unwrap().clone();
        let right_merkle = self.mt.digests.get(&key2).unwrap().clone();

        let left_canonical = match self.ct.digests.get(&key1) {
            Some(value) => value.clone(),
            None => CanonicalTree::<F, H>::default(),
        };
        let right_canonical = match self.ct.digests.get(&key2) {
            Some(value) => value.clone(),
            None => CanonicalTree::<F, H>::default(),
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
}

impl<'a> InternalProver<'a, DefF, DefH, DefC, 2> {
    pub fn from_public_params_and_inputs(data: &'a PublicParamsAndInputs) -> Self {
        Self {
            mt: &data.mt,
            ct: &data.ct,
            pp: &data.pp,
        }
    }
}

pub struct CompactProver<'a, F, C, const D: usize>
    where
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F=F> + 'static,
        C::Hasher: AlgebraicHasher<F>,
{
    pp: &'a SNARK_PP<F, C, D>,
}

impl<'a, F, C, const D: usize> CompactProver<'a, F, C, D>
    where
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F=F> + 'static,
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
}

impl<'a> CompactProver<'a, DefF, DefC, 2> {
    pub fn from_public_params_and_inputs(data: &'a PublicParamsAndInputs) -> Self {
        Self { pp: &data.pp }
    }
}