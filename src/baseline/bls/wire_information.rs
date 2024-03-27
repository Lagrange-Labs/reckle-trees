use std::collections::HashMap;

use plonky2::{
    field::extension::Extendable,
    hash::hash_types::{HashOut, HashOutTarget, RichField},
    iop::{
        target::Target,
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::config::Hasher,
};

use crate::utils::mt_binary::MerkleProof;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WireInformation<const D: usize> {
    pub(crate) digest_target: HashOutTarget,
    pub(crate) index_target: Vec<Target>,
    pub(crate) pk_target: Vec<Vec<Target>>,
    pub(crate) proof_target: Vec<Vec<HashOutTarget>>,
}
impl<const D: usize> WireInformation<D> {
    pub fn new(
        digest_target: HashOutTarget,
        index_target: &Vec<Target>,
        pk_target: &Vec<Vec<Target>>,
        proof_target: &Vec<Vec<HashOutTarget>>,
    ) -> Self {
        Self {
            digest_target: digest_target,
            index_target: index_target.to_vec(),
            pk_target: pk_target.to_vec(),
            proof_target: proof_target.to_vec(),
        }
    }
    pub fn compute_pw<F, H>(
        &self,
        digest_target: HashOut<F>,
        merkle_proofs: &HashMap<u32, (Vec<F>, MerkleProof<F, H>)>,
    ) -> PartialWitness<F>
    where
        F: RichField + Extendable<D>,
        H: Hasher<F, Hash = HashOut<F>>,
    {
        let mut pw: PartialWitness<F> = PartialWitness::new();

        pw.set_hash_target(self.digest_target, digest_target);

        for (i, (index, (leaf, proof))) in merkle_proofs.iter().enumerate() {
            let index = index.clone();
            pw.set_target(self.index_target[i], F::from_canonical_u32(index));
            pw.set_target_arr(&self.pk_target[i], leaf);
            for j in 0..proof.siblings.len() {
                pw.set_hash_target(self.proof_target[i][j], proof.siblings[j]);
            }
        }
        pw
    }
}
