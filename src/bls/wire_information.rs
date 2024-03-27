use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::{HashOut, HashOutTarget, MerkleCapTarget, RichField};
use plonky2::hash::merkle_tree::MerkleCap;
use plonky2::iop::target::Target;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig};
use plonky2::plonk::proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget};

use super::BN254_TO_U32_LIMBS;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct LeafWireInformation<const D: usize> {
    pub(crate) left_merkle_t: HashOutTarget,
    pub(crate) left_apk_t: [Target; BN254_TO_U32_LIMBS],

    pub(crate) right_merkle_t: HashOutTarget,
    pub(crate) right_apk_t: [Target; BN254_TO_U32_LIMBS],
}

impl<const D: usize> LeafWireInformation<D> {
    pub fn new(
        left_merkle_t: HashOutTarget,
        left_apk_t: &[Target],
        right_merkle_t: HashOutTarget,
        right_apk_t: &[Target],
    ) -> Self {
        Self {
            left_merkle_t,
            left_apk_t: left_apk_t
                .try_into()
                .expect("wire_information: slice with incorrect length"),
            right_merkle_t,
            right_apk_t: right_apk_t
                .try_into()
                .expect("wire_information: slice with incorrect length"),
        }
    }
    pub fn compute_pw<F>(
        &self,
        left_merkle: HashOut<F>,
        left_apk: &[F],
        right_merkle: HashOut<F>,
        right_apk: &[F],
    ) -> PartialWitness<F>
    where
        F: RichField + Extendable<D>,
    {
        let mut pw: PartialWitness<F> = PartialWitness::new();

        pw.set_hash_target(self.left_merkle_t, left_merkle);
        pw.set_target_arr(&self.left_apk_t, &left_apk);

        pw.set_hash_target(self.right_merkle_t, right_merkle);
        pw.set_target_arr(&self.right_apk_t, &right_apk);

        return pw;
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InternalWireInformation<const D: usize> {
    pub(crate) left_proof_target: ProofWithPublicInputsTarget<D>,
    pub(crate) right_proof_target: ProofWithPublicInputsTarget<D>,
    pub(crate) verifier_circuit_data_target_merkle_cap: MerkleCapTarget,
}

impl<const D: usize> InternalWireInformation<D> {
    pub fn new(
        left_proof_target: ProofWithPublicInputsTarget<D>,
        right_proof_target: ProofWithPublicInputsTarget<D>,
        verifier_circuit_data_target_merkle_cap: MerkleCapTarget,
    ) -> Self {
        Self {
            left_proof_target,
            right_proof_target,
            verifier_circuit_data_target_merkle_cap,
        }
    }

    pub fn compute_pw<F, InnerC>(
        &self,
        left_proof: ProofWithPublicInputs<F, InnerC, D>,
        right_proof: ProofWithPublicInputs<F, InnerC, D>,
        verifier_circuit_data_target_merkle_cap: MerkleCap<F, InnerC::Hasher>,
    ) -> PartialWitness<F>
    where
        F: RichField + Extendable<D>,
        InnerC: GenericConfig<D, F = F> + 'static,
        InnerC::Hasher: AlgebraicHasher<F>,
    {
        let mut pw: PartialWitness<F> = PartialWitness::new();

        pw.set_proof_with_pis_target(&self.left_proof_target, &left_proof);

        pw.set_proof_with_pis_target(&self.right_proof_target, &right_proof);

        pw.set_cap_target(
            &self.verifier_circuit_data_target_merkle_cap,
            &verifier_circuit_data_target_merkle_cap,
        );

        return pw;
    }
}

#[derive(PartialEq, Eq, Debug)]
pub struct CompactWireInformation<const D: usize> {
    pub(crate) inner_proof_target: ProofWithPublicInputsTarget<D>,
    pub(crate) inner_verifier_circuit_data_target_merkle_cap: MerkleCapTarget,
}
impl<const D: usize> CompactWireInformation<D> {
    pub fn new(
        inner_proof_target: ProofWithPublicInputsTarget<D>,
        inner_verifier_circuit_data_target_merkle_cap: MerkleCapTarget,
    ) -> Self {
        Self {
            inner_proof_target,
            inner_verifier_circuit_data_target_merkle_cap,
        }
    }
    pub fn compute_pw<F, InnerC>(
        &self,
        inner_proof: ProofWithPublicInputs<F, InnerC, D>,
        inner_verifier_circuit_data_merkle_cap: MerkleCap<F, InnerC::Hasher>,
    ) -> PartialWitness<F>
    where
        F: RichField + Extendable<D>,
        InnerC: GenericConfig<D, F = F> + 'static,
        InnerC::Hasher: AlgebraicHasher<F>,
    {
        let mut pw: PartialWitness<F> = PartialWitness::new();

        pw.set_proof_with_pis_target(&self.inner_proof_target, &inner_proof);
        pw.set_cap_target(
            &self.inner_verifier_circuit_data_target_merkle_cap,
            &inner_verifier_circuit_data_merkle_cap,
        );
        return pw;
    }
}
