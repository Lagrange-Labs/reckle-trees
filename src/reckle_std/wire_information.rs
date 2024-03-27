use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::HashOut;
use plonky2::hash::hash_types::HashOutTarget;
use plonky2::hash::hash_types::MerkleCapTarget;
use plonky2::hash::hash_types::RichField;
use plonky2::hash::merkle_tree::MerkleCap;

use plonky2::iop::witness::PartialWitness;
use plonky2::iop::witness::WitnessWrite;

use plonky2::plonk::config::AlgebraicHasher;
use plonky2::plonk::config::GenericConfig;

use plonky2::plonk::proof::ProofWithPublicInputsTarget;

use plonky2::plonk::proof::ProofWithPublicInputs;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct LeafWireInformation<const D: usize> {
    pub(crate) left_merkle_target: HashOutTarget,
    pub(crate) left_canonical_target: HashOutTarget,

    pub(crate) right_merkle_target: HashOutTarget,
    pub(crate) right_canonical_target: HashOutTarget,
}
impl<const D: usize> LeafWireInformation<D> {
    pub fn new(
        left_merkle_target: HashOutTarget,
        left_canonical_target: HashOutTarget,

        right_merkle_target: HashOutTarget,
        right_canonical_target: HashOutTarget,
    ) -> Self {
        Self {
            left_merkle_target,
            left_canonical_target,

            right_merkle_target,
            right_canonical_target,
        }
    }
    pub fn compute_pw<F>(
        &self,
        left_merkle: HashOut<F>,
        left_canonical: HashOut<F>,

        right_merkle: HashOut<F>,
        right_canonical: HashOut<F>,
    ) -> PartialWitness<F>
    where
        F: RichField + Extendable<D>,
    {
        let mut pw: PartialWitness<F> = PartialWitness::new();

        pw.set_hash_target(self.left_merkle_target, left_merkle);
        pw.set_hash_target(self.left_canonical_target, left_canonical);

        pw.set_hash_target(self.right_merkle_target, right_merkle);
        pw.set_hash_target(self.right_canonical_target, right_canonical);

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
