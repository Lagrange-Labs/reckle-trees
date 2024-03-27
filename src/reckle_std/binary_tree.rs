use log::info;

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig};
use plonky2::plonk::proof::ProofWithPublicInputs;

use crate::reckle_std::binary_pp::SNARK_PP;
use crate::reckle_std::provers::{CompactProver, InternalProver, LeafProver};
use crate::utils::canonical::CanonicalTree;
use crate::utils::mt_binary::{MerkleProof, PartialMT};

pub struct RecDS<F, C, const D: usize>
where
    C: GenericConfig<D, F = F> + 'static,
    F: RichField + Extendable<D>,
    C::Hasher: AlgebraicHasher<F>,
{
    pub leaves: HashMap<u32, Vec<F>>,

    pub mt: PartialMT<F, C::Hasher>,     // Merkle tree
    pub ct: CanonicalTree<F, C::Hasher>, // Canonical digest tree
    pub proofs: HashMap<(u8, u32), ProofWithPublicInputs<F, C, D>>, // Recursive proof tree

    pub proofs_compact: HashMap<u8, ProofWithPublicInputs<F, C, D>>,
}

impl<F, C, const D: usize> RecDS<F, C, D>
where
    C: GenericConfig<D, F = F> + 'static,
    F: RichField + Extendable<D>,
    C::Hasher: AlgebraicHasher<F>,
{
    // Synonymous with aggregation
    pub fn new(
        pp: &SNARK_PP<F, C, D>,
        merkle_proofs: HashMap<u32, (Vec<F>, MerkleProof<F, C::Hasher>)>,
    ) -> Self
    where
        C::Hasher: AlgebraicHasher<F>,
    {
        let leaves = Self::get_leaves_map(&merkle_proofs);
        let mt = PartialMT::from_proofs(&merkle_proofs);
        let ct = CanonicalTree::new(mt.log_max_capacity, &leaves);
        info!("=== Building SNARKs tree");
        let (proofs, proofs_compact) = Self::build_SNARK_tree(&pp, &leaves, &mt, &ct);
        info!("=== Done building SNARKs tree");

        Self {
            leaves,
            mt,
            ct,
            proofs,
            proofs_compact,
        }
    }

    pub fn get_leaves_map(
        merkle_proofs: &HashMap<u32, (Vec<F>, MerkleProof<F, C::Hasher>)>,
    ) -> HashMap<u32, Vec<F>> {
        let mut leaves: HashMap<u32, Vec<F>> = HashMap::new();
        for (k, v) in merkle_proofs {
            let index = k.clone();
            let leaf_data = v.0.clone();
            leaves.insert(index, leaf_data);
        }
        leaves
    }

    #[allow(non_snake_case)]
    pub fn build_SNARK_tree(
        pp: &SNARK_PP<F, C, D>,
        leaves: &HashMap<u32, Vec<F>>,
        mt: &PartialMT<F, C::Hasher>,
        ct: &CanonicalTree<F, C::Hasher>,
    ) -> (
        HashMap<(u8, u32), ProofWithPublicInputs<F, C, D>>,
        HashMap<u8, ProofWithPublicInputs<F, C, D>>,
    )
    where
        C::Hasher: AlgebraicHasher<F>,
    {
        let mut indices: HashSet<u32> = HashSet::new();
        for index in leaves.keys() {
            indices.insert(index.clone() >> 1);
        }

        let mut proof: ProofWithPublicInputs<F, C, D>;
        let mut proofs: HashMap<(u8, u32), ProofWithPublicInputs<F, C, D>> = HashMap::new();
        let mut proofs_compact: HashMap<u8, ProofWithPublicInputs<F, C, D>> = HashMap::new();

        let mut leaf_prover = LeafProver::new(&pp, mt, ct);
        for i in &indices {
            let key: (u8, u32) = (1, i.clone());

            let pw = leaf_prover.compute_pw(*i);
            let proof = leaf_prover.prove(pw).unwrap();

            proofs.insert(key, proof);
        }
        info!("====== Proved level {}/{}", 1, pp.log_max_capacity);

        indices = HashSet::from_iter(indices.into_iter().map(|i| i >> 1));

        let mut internal_prover = InternalProver::new(&pp, mt, ct);

        for i in 2..=pp.log_max_capacity {
            let internal_config_index = (i - 2) as usize;
            for j in &indices {
                let key = (i, *j);
                let key1: (u8, u32) = (i - 1, 2 * (*j));
                let key2: (u8, u32) = (i - 1, 2 * (*j) + 1);

                let pw = internal_prover.compute_pw(
                    key,
                    proofs.get(&key1).cloned(),
                    proofs.get(&key2).cloned(),
                );

                proof = internal_prover.prove(internal_config_index, pw).unwrap();

                proofs.insert(key, proof);
            }
            indices = HashSet::from_iter(indices.into_iter().map(|i| i >> 1));
            info!("====== Proved level {}/{}", i, pp.log_max_capacity);
        }

        let key: (u8, u32) = (pp.log_max_capacity, 0);
        proof = proofs.get(&key).clone().unwrap().clone();

        let mut compact_prover = CompactProver::new(pp);

        for i in 0..pp.compaction_level {
            let i_usize = i as usize;
            let pw = compact_prover.compute_pw(i_usize, proof);

            proof = compact_prover.prove(i_usize, pw).unwrap();
            proofs_compact.insert(i, proof.clone());
            info!(
                "====== Proved level {}/{}",
                pp.log_max_capacity + i + 1,
                pp.log_max_capacity
            );
        }

        (proofs, proofs_compact)
    }

    pub fn update_tree(&mut self, pp: &SNARK_PP<F, C, D>, updated_index: u32, updated_value: Vec<F>)
    where
        C::Hasher: AlgebraicHasher<F>,
    {
        self.leaves.insert(updated_index, updated_value.clone());

        self.mt.update_tree(updated_index, updated_value.clone());
        self.ct.update_tree(updated_index, updated_value.clone());

        let mut updated_index = updated_index >> 1;
        let mut proof: ProofWithPublicInputs<F, C, D>;

        {
            let key: (u8, u32) = (1, updated_index.clone());

            let mut leaf_prover = LeafProver::new(pp, &self.mt, &self.ct);
            let pw = leaf_prover.compute_pw(updated_index);

            let now = Instant::now();
            proof = leaf_prover.prove(pw).unwrap();
            let elapsed = now.elapsed();
            info!(
                "====== Update: Prove level {}/{}: {:?}",
                1, pp.log_max_capacity, elapsed
            );
            self.proofs.insert(key, proof);
        }

        updated_index = updated_index >> 1;

        {
            let mut internal_prover = InternalProver::new(pp, &self.mt, &self.ct);

            for i in 2..=pp.log_max_capacity {
                let internal_config_index = (i - 2) as usize;

                let key = (i, updated_index);
                let key1: (u8, u32) = (i - 1, 2 * (updated_index));
                let key2: (u8, u32) = (i - 1, 2 * (updated_index) + 1);

                let pw = internal_prover.compute_pw(
                    key,
                    self.proofs.get(&key1).cloned(),
                    self.proofs.get(&key2).cloned(),
                );

                let now = Instant::now();
                proof = internal_prover.prove(internal_config_index, pw).unwrap();
                let elapsed = now.elapsed();
                info!(
                    "====== Update: Prove level {}/{}: {:?}",
                    i, pp.log_max_capacity, elapsed
                );
                self.proofs.insert(key, proof);

                updated_index = updated_index >> 1;
            }
        }
        {
            let key: (u8, u32) = (pp.log_max_capacity, 0);
            proof = self.proofs.get(&key).clone().unwrap().clone();

            let mut compact_prover = CompactProver::new(pp);

            for i in 0..pp.compaction_level {
                let i_usize = i as usize;
                let pw = compact_prover.compute_pw(i_usize, proof);

                let now = Instant::now();
                proof = compact_prover.prove(i_usize, pw).unwrap();
                let elapsed = now.elapsed();
                info!(
                    "====== Update: Prove level {}/{}: {:?}",
                    pp.log_max_capacity + i + 1,
                    pp.log_max_capacity,
                    elapsed
                );

                self.proofs_compact.insert(i, proof.clone());
            }
        }
    }

    pub fn get_recproof(&self) -> ProofWithPublicInputs<F, C, D> {
        let proof = self
            .proofs_compact
            .iter()
            .max_by_key(|&(k, _v)| k)
            .map(|(_, v)| v)
            .unwrap()
            .clone();
        return proof;
    }

    pub fn size_by_level(&self, pp: &SNARK_PP<F, C, D>, updated_index: u32)
    where
        C::Hasher: AlgebraicHasher<F>,
    {
        let mut updated_index = updated_index >> 1;
        {
            let key: (u8, u32) = (1, updated_index.clone());
            let proof = self.proofs.get(&key).unwrap();
            let compressed_proof = proof
                .clone()
                .compress(
                    &pp.verifier_leaf.verifier_only.circuit_digest,
                    &pp.common_leaf,
                )
                .unwrap();
            println!(
                "==== {}/{} proof size: {:>6.2} KiB. compressed size: {:>6.2} KiB",
                1,
                pp.log_max_capacity,
                proof.to_bytes().len() as f32 / 1024.0,
                compressed_proof.to_bytes().len() as f32 / 1024.0
            );
        }

        updated_index = updated_index >> 1;

        {
            for i in 2..=pp.log_max_capacity {
                let internal_config_index = (i - 2) as usize;
                let key = (i, updated_index);
                let proof = self.proofs.get(&key).unwrap();
                let compressed_proof = proof
                    .clone()
                    .compress(
                        &pp.verifier_internal[internal_config_index]
                            .verifier_only
                            .circuit_digest,
                        &pp.common_internal[internal_config_index],
                    )
                    .unwrap();

                println!(
                    "==== {}/{} proof size: {:>6.2} KiB. compressed size: {:>6.2} KiB",
                    i,
                    pp.log_max_capacity,
                    proof.to_bytes().len() as f32 / 1024.0,
                    compressed_proof.to_bytes().len() as f32 / 1024.0
                );

                updated_index = updated_index >> 1;
            }
        }
        {
            for i in 0..pp.compaction_level {
                let proof = self.proofs_compact.get(&i).unwrap();
                let compressed_proof = proof
                    .clone()
                    .compress(
                        &pp.verifier_compact[i as usize].verifier_only.circuit_digest,
                        &pp.common_compact[i as usize],
                    )
                    .unwrap();
                println!(
                    "==== {}/{} proof size: {:>6.2} KiB, compressed size: {:>6.2} KiB",
                    pp.log_max_capacity + i + 1,
                    pp.log_max_capacity,
                    proof.to_bytes().len() as f32 / 1024.0,
                    compressed_proof.to_bytes().len() as f32 / 1024.0
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::collections::HashSet;
    use std::time::Instant;

    use plonky2::field::extension::Extendable;
    use plonky2::hash::hash_types::RichField;

    use plonky2::plonk::config::AlgebraicHasher;
    use plonky2::plonk::config::GenericConfig;
    use plonky2::plonk::config::PoseidonGoldilocksConfig;
    use rand::rngs::StdRng;
    use rand::seq::IteratorRandom;
    use rand::SeedableRng;

    use crate::reckle_std::benches::rec_worker;
    use crate::reckle_std::binary_pp::SNARK_PP;
    use crate::utils::mt_binary::MerkleProof;
    use crate::utils::mt_binary::PartialMT;

    use super::RecDS;

    use log::LevelFilter;

    fn rec_test_base<F, C, const D: usize>(log_tree_size: u8, log_subset_size: u8)
    where
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F = F> + 'static,
        C::Hasher: AlgebraicHasher<F>,
    {
        let mut r: StdRng = StdRng::seed_from_u64(223);
        let tree_size: u32 = 1 << log_tree_size;
        let subset_size: u32 = 1 << log_subset_size;

        let subset_indices: HashSet<u32> =
            HashSet::from_iter((0..tree_size).choose_multiple(&mut r, subset_size as usize));

        let mut subset_indices_vec = Vec::from_iter(subset_indices.clone());
        subset_indices_vec.sort();

        println!("=== Sorted indices: {:?}", subset_indices_vec);

        let leaves: HashMap<u32, Vec<F>> = subset_indices
            .clone()
            .into_iter()
            .map(|i| (i as u32, F::rand_vec(5)))
            .collect::<HashMap<_, _>>();

        let now = Instant::now();
        let pp = SNARK_PP::<F, C, D>::setup(log_tree_size);
        let elapsed = now.elapsed();
        println!("=== Setup done in {:?}", elapsed);

        let mt = PartialMT::<F, C::Hasher>::new(log_tree_size, &leaves);
        let mut merkle_proofs: HashMap<u32, (Vec<F>, MerkleProof<F, C::Hasher>)> = HashMap::new();
        for (k, v) in &leaves {
            let mt_proof = mt.prove(*k);
            merkle_proofs.insert(*k, (v.clone(), mt_proof));
        }
        println!("=== Get individual proofs of the subset");

        let now = Instant::now();
        let mut rec_ds = RecDS::<F, C, D>::new(&pp, merkle_proofs);
        let elapsed = now.elapsed();
        println!("=== Prove done in {:?}", elapsed);

        let updated_index = subset_indices_vec.iter().choose(&mut r).unwrap().clone();
        let updated_value = F::rand_vec(5);

        let now = Instant::now();
        rec_ds.update_tree(&pp, updated_index, updated_value);
        let elapsed = now.elapsed();
        println!(
            "=== Update done to index {:?} in {:?}",
            updated_index, elapsed
        );

        println!("=== Proof sizes");
        rec_ds.size_by_level(&pp, updated_index);

        println!("=== Public parameter sizes");
        pp.size_by_level();
    }

    #[test]
    fn rec_test_1() {
        env_logger::init();
        log::set_max_level(LevelFilter::Debug);

        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let ell: u8 = 5;
        let log_subset_size: u8 = 4;
        rec_test_base::<F, C, D>(ell, log_subset_size);
    }

    #[test]
    fn rec_benches() {
        env_logger::init();
        log::set_max_level(LevelFilter::Debug);

        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        rec_worker::<F, C, D>();
    }
}
