use std::collections::HashMap;
use std::time::Instant;

use log::info;
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, Hasher};
use plonky2::plonk::proof::ProofWithPublicInputs;

use crate::digest_translation::binary_pp::SNARK_PP;
use crate::digest_translation::provers::{CompactProver, InternalProver, LeafProver};

use crate::utils::mt_binary::PartialMT;

pub struct DigestTranslationDS<F, C, KH, PH, const D: usize>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
    KH: Hasher<F>,
    PH: AlgebraicHasher<F>,
{
    pub leaves: HashMap<u32, Vec<F>>,

    pub mt_kh: PartialMT<F, KH>,
    pub mt_ph: PartialMT<F, PH>,

    pub proofs: HashMap<(u8, u32), ProofWithPublicInputs<F, C, D>>,

    pub proofs_compact: HashMap<u8, ProofWithPublicInputs<F, C, D>>,
}

impl<F, C, KH, PH, const D: usize> DigestTranslationDS<F, C, KH, PH, D>
where
    C: GenericConfig<D, F = F> + 'static,
    F: RichField + Extendable<D>,
    C::Hasher: AlgebraicHasher<F>,
    KH: Hasher<F>,
    PH: AlgebraicHasher<F>,
{
    pub fn new(pp: &SNARK_PP<F, C, D>, leaves: HashMap<u32, Vec<F>>) -> Self {
        let tree_size = (1 << pp.log_max_capacity) as usize;
        assert!(tree_size == leaves.len());

        let mt_kh = PartialMT::<F, KH>::new(pp.log_max_capacity, &leaves);
        let mt_ph = PartialMT::<F, PH>::new(pp.log_max_capacity, &leaves);

        let (proofs, proofs_compact) = Self::build_SNARK_tree(&pp, &mt_kh, &mt_ph);

        Self {
            leaves: leaves,
            mt_kh,
            mt_ph,
            proofs,
            proofs_compact,
        }
    }

    #[allow(non_snake_case)]
    pub fn build_SNARK_tree(
        pp: &SNARK_PP<F, C, D>,
        mt_kh: &PartialMT<F, KH>,
        mt_ph: &PartialMT<F, PH>,
    ) -> (
        HashMap<(u8, u32), ProofWithPublicInputs<F, C, D>>,
        HashMap<u8, ProofWithPublicInputs<F, C, D>>,
    ) {
        let mut proof: ProofWithPublicInputs<F, C, D>;
        let mut proofs: HashMap<(u8, u32), ProofWithPublicInputs<F, C, D>> = HashMap::new();
        let mut proofs_compact: HashMap<u8, ProofWithPublicInputs<F, C, D>> = HashMap::new();

        let mut current_level_size = (1 << (pp.log_max_capacity - 1)) as u32;

        let mut leaf_prover = LeafProver::new(&pp, mt_kh, mt_ph);

        for i in 0..current_level_size {
            let key: (u8, u32) = (1, i.clone());
            let pw = leaf_prover.compute_pw(i);
            let proof = leaf_prover.prove(pw).unwrap();

            proofs.insert(key, proof);
        }

        let mut internal_prover = InternalProver::<F, C, KH, PH, D>::new(&pp, mt_kh, mt_ph);

        for i in 2..=pp.log_max_capacity {
            let internal_config_index = (i - 2) as usize;

            current_level_size = current_level_size / 2;
            for j in 0..current_level_size {
                let key = (i, j);
                let key1: (u8, u32) = (i - 1, 2 * (j));
                let key2: (u8, u32) = (i - 1, 2 * (j) + 1);

                let pw = internal_prover.compute_pw(
                    key,
                    proofs.get(&key1).cloned(),
                    proofs.get(&key2).cloned(),
                );

                proof = internal_prover.prove(internal_config_index, pw).unwrap();

                proofs.insert(key, proof);
            }
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
        pp: &SNARK_PP<F, C, D>,
        updated_index: u32,
        updated_value: Vec<F>,
    ) {
        self.leaves.insert(updated_index, updated_value.clone());

        self.mt_ph.update_tree(updated_index, updated_value.clone());
        self.mt_kh.update_tree(updated_index, updated_value.clone());

        let mut updated_index = updated_index >> 1;
        let mut proof: ProofWithPublicInputs<F, C, D>;

        {
            let key: (u8, u32) = (1, updated_index.clone());
            let mut leaf_prover = LeafProver::new(pp, &self.mt_kh, &self.mt_ph);
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
            let mut internal_prover = InternalProver::new(pp, &self.mt_kh, &self.mt_ph);

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

    pub fn size_by_level(&self, pp: &SNARK_PP<F, C, D>, updated_index: u32) {
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
    use log::LevelFilter;

    use plonky2::hash::keccak::KeccakHash;
    use plonky2::hash::poseidon::PoseidonHash;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    use crate::digest_translation::benches::dt_worker;

    #[test]
    fn dt_benches() {
        env_logger::init();
        log::set_max_level(LevelFilter::Debug);

        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type KH = KeccakHash<32>;
        type PH = PoseidonHash;

        dt_worker::<F, C, KH, PH, D>();
    }
}
