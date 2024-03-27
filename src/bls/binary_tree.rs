use std::collections::{HashMap, HashSet};
use std::time::Instant;

use log::info;
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::config::GenericConfig;
use plonky2::plonk::proof::ProofWithPublicInputs;

use plonky2::hash::hash_types::HashOut;
use plonky2::plonk::config::AlgebraicHasher;

use crate::bls::binary_pp::SNARK_PP;
use crate::bls::provers::{CompactProver, InternalProver, LeafProver};
use crate::utils::mt_binary::PartialMT;

pub struct BlsDS<const Q: usize, F, C, const D: usize>
where
    C: GenericConfig<D, F = F> + 'static,
    F: RichField + Extendable<D>,
    C::Hasher: AlgebraicHasher<F, Hash = HashOut<F>>,
{
    pub leaves: HashMap<u32, Vec<F>>,

    pub mt: PartialMT<F, C::Hasher>, // Merkle tree
    pub proofs: HashMap<(u8, u32), ProofWithPublicInputs<F, C, D>>, // Recursive proof tree

    pub proofs_compact: HashMap<u8, ProofWithPublicInputs<F, C, D>>,
}

impl<const Q: usize, F, C, const D: usize> BlsDS<Q, F, C, D>
where
    C: GenericConfig<D, F = F> + 'static,
    F: RichField + Extendable<D>,
    C::Hasher: AlgebraicHasher<F, Hash = HashOut<F>>,
    [(); 1 << Q]:,
{
    pub fn new(log_tree_size: u8, pp: &SNARK_PP<Q, F, C, D>, leaves: HashMap<u32, Vec<F>>) -> Self {
        assert!(Q == 1);
        let mt: PartialMT<F, C::Hasher> = PartialMT::new_bucket(Q, log_tree_size, &leaves);

        let (proofs, proofs_compact) = Self::build_SNARK_tree(&pp, &leaves, &mt);
        Self {
            leaves,
            mt,
            proofs,
            proofs_compact,
        }
    }

    #[allow(non_snake_case)]
    pub fn build_SNARK_tree(
        pp: &SNARK_PP<Q, F, C, D>,
        leaves: &HashMap<u32, Vec<F>>,
        mt: &PartialMT<F, C::Hasher>,
    ) -> (
        HashMap<(u8, u32), ProofWithPublicInputs<F, C, D>>,
        HashMap<u8, ProofWithPublicInputs<F, C, D>>,
    ) {
        let mut indices: HashSet<u32> = HashSet::new();
        for index in leaves.keys() {
            indices.insert(index.clone() >> Q);
        }

        let mut proof: ProofWithPublicInputs<F, C, D>;
        let mut proofs: HashMap<(u8, u32), ProofWithPublicInputs<F, C, D>> = HashMap::new();
        let mut proofs_compact: HashMap<u8, ProofWithPublicInputs<F, C, D>> = HashMap::new();

        let mut leaf_prover = LeafProver::new(&leaves, &pp, mt);
        for i in &indices {
            let key: (u8, u32) = (Q as u8, i.clone());
            let pw = leaf_prover.compute_pw(*i);

            let proof = leaf_prover.prove(pw).unwrap();
            proofs.insert(key, proof);
        }

        indices = HashSet::from_iter(indices.into_iter().map(|i| i >> 1));

        let mut internal_prover = InternalProver::new(&pp, mt);

        for i in (Q as u8 + 1)..=pp.log_max_capacity {
            let internal_config_index = i as usize - (Q + 1);
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
        }

        let key: (u8, u32) = (pp.log_max_capacity, 0);
        proof = proofs.get(&key).clone().unwrap().clone();

        let mut compact_prover = CompactProver::new(pp);

        for i in 0..pp.compaction_level {
            let i_usize = i as usize;
            let pw = compact_prover.compute_pw(i_usize, proof);

            proof = compact_prover.prove(i_usize, pw).unwrap();
            proofs_compact.insert(i, proof.clone());
        }

        (proofs, proofs_compact)
    }

    pub fn update_tree(
        &mut self,
        pp: &SNARK_PP<Q, F, C, D>,
        updated_index: u32,
        updated_value: Vec<F>,
    ) {
        assert!(Q == 1);
        self.leaves.insert(updated_index, updated_value.clone());

        self.mt.update_tree(updated_index, updated_value.clone());

        let mut updated_index = updated_index >> Q;
        let mut proof: ProofWithPublicInputs<F, C, D>;

        {
            let key: (u8, u32) = (Q as u8, updated_index.clone());

            let mut leaf_prover = LeafProver::new(&self.leaves, pp, &self.mt);
            let pw = leaf_prover.compute_pw(updated_index);

            let now = Instant::now();
            let proof = leaf_prover.prove(pw).unwrap();
            let elapsed = now.elapsed();
            info!(
                "====== Update: Prove level {}/{}: {:?}",
                Q, pp.log_max_capacity, elapsed
            );
            self.proofs.insert(key, proof);
        }

        updated_index = updated_index >> 1;

        {
            let mut internal_prover = InternalProver::new(pp, &self.mt);

            for i in (Q as u8 + 1)..=pp.log_max_capacity {
                let internal_config_index = i as usize - (Q + 1);

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

    pub fn size_by_level(&self, pp: &SNARK_PP<Q, F, C, D>, updated_index: u32) {
        let mut updated_index = updated_index >> Q;
        {
            let key: (u8, u32) = (Q as u8, updated_index.clone());
            let proof = self.proofs.get(&key).unwrap();
            let compressed_proof = proof
                .clone()
                .compress(
                    &pp.verifier_leaf.verifier_only.circuit_digest,
                    &pp.common_leaf,
                )
                .unwrap();
            println!(
                "{}/{} proof size: {:.2} KiB. compressed size: {:.2} KiB",
                Q,
                pp.log_max_capacity,
                proof.to_bytes().len() as f32 / 1024.0,
                compressed_proof.to_bytes().len() as f32 / 1024.0
            );
        }

        updated_index = updated_index >> 1;

        {
            for i in (Q as u8 + 1)..=pp.log_max_capacity {
                let internal_config_index = i as usize - (Q + 1);
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
                    "{}/{} proof size: {:.2} KiB. compressed size: {:.2} KiB",
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
                    "{}/{} proof size: {:.2} KiB. compressed size: {:.2} KiB",
                    pp.log_max_capacity + i + 1,
                    pp.log_max_capacity,
                    proof.to_bytes().len() as f32 / 1024.0,
                    compressed_proof.to_bytes().len() as f32 / 1024.0
                );
            }
        }
    }
}
mod tests {
    #[test]
    fn bls_benches() {
        env_logger::init();
        log::set_max_level(log::LevelFilter::Debug);

        const D: usize = 2;
        type C = plonky2::plonk::config::PoseidonGoldilocksConfig;
        type F = <C as plonky2::plonk::config::GenericConfig<D>>::F;
        const Q: usize = 1;

        crate::bls::benches::bls_worker::<Q, F, C, D>();
    }
}
