use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::{MerkleCapTarget, RichField, NUM_HASH_OUT_ELTS};
use plonky2::hash::merkle_tree::MerkleCap;
use plonky2::iop::target::Target;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig};
use plonky2::plonk::proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct LeafWireInformation<const D: usize> {
    pub(crate) left_data_target: [Target; NUM_HASH_OUT_ELTS],
    pub(crate) right_data_target: [Target; NUM_HASH_OUT_ELTS],
}
impl<const D: usize> LeafWireInformation<D> {
    pub fn new(
        left_data_target: [Target; NUM_HASH_OUT_ELTS],
        right_data_target: [Target; NUM_HASH_OUT_ELTS],
    ) -> Self {
        Self {
            left_data_target,
            right_data_target,
        }
    }
    pub fn compute_pw<F>(&self, left_data: &[F], right_data: &[F]) -> PartialWitness<F>
    where
        F: RichField + Extendable<D>,
    {
        let mut pw: PartialWitness<F> = PartialWitness::new();

        pw.set_target_arr(&self.left_data_target, left_data);
        pw.set_target_arr(&self.right_data_target, right_data);
        pw
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
