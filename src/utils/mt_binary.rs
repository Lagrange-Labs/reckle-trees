use itertools::Itertools;
use num_traits::ToPrimitive;
use std::collections::{HashMap, HashSet};

use plonky2::hash::hash_types::RichField;
use plonky2::plonk::config::GenericHashOut;
use plonky2::plonk::config::Hasher;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MerkleProof<F: RichField, H: Hasher<F>> {
    /// The Merkle digest of each sibling subtree, staying from the bottom most layer.
    pub siblings: Vec<H::Hash>,
}

impl<F: RichField, H: Hasher<F>> MerkleProof<F, H> {
    pub fn len(&self) -> usize {
        self.siblings.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[derive(Clone)]
pub struct MerkleBucketProof<F: RichField, H: Hasher<F>> {
    /// The Merkle digest of each sibling subtree, staying from the bottom most layer.
    pub siblings: Vec<H::Hash>, // Regular siblings
    pub bucket_siblings: Vec<H::Hash>, // siblings in the lowest level
}

impl<F: RichField, H: Hasher<F>> MerkleBucketProof<F, H> {
    pub fn bucket_size(&self) -> usize {
        self.bucket_siblings.len()
    }

    pub fn len(&self) -> usize {
        self.siblings.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0 && self.bucket_size() == 0
    }
}

/// Note: Saves H(data). Assumes that the caller knows `data`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PartialMT<F: RichField, H: Hasher<F>> {
    pub log_max_capacity: u8, // Indexed from 0
    pub digests: HashMap<(u8, u32), H::Hash>,
}

impl<F: RichField, H: Hasher<F>> PartialMT<F, H> {
    pub fn default() -> H::Hash {
        H::Hash::from_bytes(&vec![0; H::HASH_SIZE])
    }

    // Assumes unknown sibling to be H(0)
    pub fn new(log_max_capacity: u8, leaves: &HashMap<u32, Vec<F>>) -> Self {
        let mut indices: HashSet<u32> = HashSet::new();
        let mut digests: HashMap<(u8, u32), H::Hash> = HashMap::new();

        for (index, value) in leaves {
            indices.insert(index.clone() >> 1);
            digests.insert((0, index.clone()), H::hash_or_noop(&value));
        }

        for i in 1..log_max_capacity + 1 as u8 {
            for j in &indices {
                let key1: (u8, u32) = (i - 1, 2 * (*j));
                let key2: (u8, u32) = (i - 1, 2 * (*j) + 1);
                let key = (i, *j);

                let left = digests.entry(key1).or_insert(Self::default()).clone();
                let right = digests.entry(key2).or_insert(Self::default()).clone();

                let parent = H::two_to_one(left, right);
                digests.insert(key, parent);
            }
            indices = HashSet::from_iter(indices.into_iter().map(|i| i >> 1));
        }
        Self {
            log_max_capacity,
            digests,
        }
    }

    pub fn prove(&self, leaf_index: u32) -> MerkleProof<F, H> {
        let mut leaf_index = leaf_index;
        let mut siblings = Vec::new();

        for i in 0..self.log_max_capacity {
            let key: (u8, u32) = if leaf_index % 2 == 0 {
                (i, leaf_index + 1)
            } else {
                (i, leaf_index - 1)
            };
            siblings.push(self.digests.get(&key).unwrap().clone());
            leaf_index = leaf_index >> 1;
        }
        MerkleProof { siblings }
    }

    pub fn prove_bucket(&self, log_bucket_size: usize, leaf_index: u32) -> MerkleBucketProof<F, H> {
        let bucket_size = (1 << log_bucket_size) as usize;
        let bucket_index = leaf_index as usize / bucket_size;
        let merkle_proof = self.prove(leaf_index);
        let h = merkle_proof.siblings.len();

        println!("{}: {:?}", leaf_index, merkle_proof.siblings);
        let siblings = merkle_proof
            .siblings
            .into_iter()
            .rev()
            .take(h - log_bucket_size)
            .rev()
            .collect_vec();
        let start_index = bucket_size * bucket_index;
        let end_index = bucket_size * (bucket_index + 1);
        let bucket_siblings = (start_index..end_index)
            .into_iter()
            .map(|i| {
                let key = (0 as u8, i as u32);
                self.digests.get(&key).unwrap().clone()
            })
            .collect_vec();
        MerkleBucketProof {
            siblings,
            bucket_siblings,
        }
    }

    pub fn verify(
        merkle_root: H::Hash,
        leaf_index: u32,
        leaf_data: &Vec<F>,
        proof: &MerkleProof<F, H>,
    ) -> bool {
        let mut index = leaf_index;
        let mut current_digest = H::hash_or_noop(&leaf_data);
        for &sibling_digest in proof.siblings.iter() {
            let bit = index & 1;
            index >>= 1;
            current_digest = if bit == 1 {
                let result = H::two_to_one(sibling_digest, current_digest);
                result
            } else {
                let result = H::two_to_one(current_digest, sibling_digest);
                result
            }
        }
        assert!(current_digest == merkle_root, "Invalid Merkle proof.");
        true
    }

    pub fn get_digest(&self) -> H::Hash {
        self.digests
            .get(&(self.log_max_capacity, 0))
            .unwrap()
            .clone()
    }

    pub fn get_digest_bytes(&self) -> Vec<u8> {
        let digest = self.get_digest();
        let digest_bytes = H::Hash::to_bytes(&digest);
        digest_bytes
    }

    pub fn from_proofs(proofs: &HashMap<u32, (Vec<F>, MerkleProof<F, H>)>) -> Self {
        let mut level = 0 as u8;
        let mut digests: HashMap<(u8, u32), H::Hash> = HashMap::new();

        for (k, v) in proofs {
            let mut index = k.clone();
            let leaf_data = v.0.clone();
            let proof = v.1.clone();
            let mut current_digest = H::hash_or_noop(&leaf_data);
            level = 0;
            for &sibling_digest in proof.siblings.iter() {
                let bit = index & 1;
                current_digest = if bit == 1 {
                    digests.insert((level, index - 1), sibling_digest.clone());
                    digests.insert((level, index), current_digest.clone());
                    let result = H::two_to_one(sibling_digest, current_digest);
                    result
                } else {
                    digests.insert((level, index), current_digest.clone());
                    digests.insert((level, index + 1), sibling_digest.clone());
                    let result = H::two_to_one(current_digest, sibling_digest);
                    result
                };
                index >>= 1;
                level = level + 1;
            }
            digests.insert((level, index), current_digest.clone());
        }
        Self {
            log_max_capacity: level,
            digests,
        }
    }

    pub fn update_tree(&mut self, updated_index: u32, updated_value: Vec<F>) {
        let mut leaf_index = updated_index;

        self.digests
            .insert((0, leaf_index.clone()), H::hash_or_noop(&updated_value));

        for i in 1..self.log_max_capacity + 1 as u8 {
            leaf_index = leaf_index >> 1;
            let key1: (u8, u32) = (i - 1, 2 * (leaf_index));
            let key2: (u8, u32) = (i - 1, 2 * (leaf_index) + 1);
            let key = (i, leaf_index);

            let left = self.digests.entry(key1).or_insert(Self::default()).clone();
            let right = self.digests.entry(key2).or_insert(Self::default()).clone();

            let parent = H::two_to_one(left, right);
            self.digests.insert(key, parent);
        }
    }

    pub fn new_bucket(
        log_bucket_size: usize,
        log_max_capacity: u8,
        leaves: &HashMap<u32, Vec<F>>,
    ) -> Self {
        assert!(log_bucket_size <= log_max_capacity as usize);

        let bucket_size = (1 << log_bucket_size) as u32;
        let mut indices: HashSet<u32> = HashSet::new();
        let mut digests: HashMap<(u8, u32), H::Hash> = HashMap::new();

        let buckets = leaves
            .iter()
            .map(|(x, _)| x / bucket_size)
            .collect::<HashSet<u32>>();

        for index_bucket in buckets {
            let start_index = bucket_size * index_bucket;
            let end_index = bucket_size * (index_bucket + 1);
            for index in start_index..end_index {
                indices.insert(index.clone() >> 1);
                digests.insert((0, index.clone()), Self::default());
            }
        }

        for (index, value) in leaves {
            indices.insert(index.clone() >> 1);
            digests.insert((0, index.clone()), H::hash_or_noop(&value));
        }

        for i in 1..log_max_capacity + 1 as u8 {
            for j in &indices {
                let key1: (u8, u32) = (i - 1, 2 * (*j));
                let key2: (u8, u32) = (i - 1, 2 * (*j) + 1);
                let key = (i, *j);

                let left = digests.entry(key1).or_insert(Self::default()).clone();
                let right = digests.entry(key2).or_insert(Self::default()).clone();

                let parent = H::two_to_one(left, right);
                digests.insert(key, parent);
            }
            indices = HashSet::from_iter(indices.into_iter().map(|i| i >> 1));
        }

        Self {
            log_max_capacity,
            digests,
        }
    }

    pub fn from_bucket_proofs(proofs: &HashMap<u32, (Vec<F>, MerkleBucketProof<F, H>)>) -> Self {
        let mut level = 0 as u8;
        let mut digests: HashMap<(u8, u32), H::Hash> = HashMap::new();
        let mut visited_bucket = HashSet::<usize>::new();
        for (k, v) in proofs {
            let mut leaf_index = k.clone();
            let leaf_data = v.0.clone();
            let proof = v.1.clone();
            let bucket_size = proof.bucket_siblings.len();
            let bucket_index = leaf_index as usize / bucket_size;

            let log_bucket_size = (bucket_size as f64).log2().to_usize().unwrap();
            let mut current_digest: H::Hash;

            visited_bucket.insert(bucket_index);
            let start_index = bucket_index * bucket_size;
            let end_index = (bucket_index + 1) * bucket_size;
            for array_index in start_index..end_index {
                digests.insert(
                    (0, array_index as u32),
                    proof.bucket_siblings[array_index - start_index].clone(),
                );
            }

            let mut prev_hash_vec = proof.bucket_siblings.clone();
            let mut prev_start = (start_index as u32) >> 1;
            level = 1 as u8;
            let mut n = prev_hash_vec.len();
            current_digest = H::hash_or_noop(&leaf_data);
            while n > 1 {
                prev_hash_vec = (0..n / 2)
                    .into_iter()
                    .map(|i| {
                        current_digest =
                            H::two_to_one(prev_hash_vec[2 * i], prev_hash_vec[2 * i + 1]);
                        let key = (level, i as u32 + prev_start);
                        digests.insert(key, current_digest);
                        current_digest
                    })
                    .collect_vec();
                leaf_index >>= 1;
                prev_start >>= 1;
                level = level + 1;
                n = prev_hash_vec.len();
            }

            level = log_bucket_size as u8;
            for &sibling_digest in proof.siblings.iter() {
                let bit = leaf_index & 1;
                current_digest = if bit == 1 {
                    digests.insert((level, leaf_index - 1), sibling_digest.clone());
                    digests.insert((level, leaf_index), current_digest.clone());

                    let result = H::two_to_one(sibling_digest, current_digest);
                    result
                } else {
                    digests.insert((level, leaf_index), current_digest.clone());
                    digests.insert((level, leaf_index + 1), sibling_digest.clone());
                    let result = H::two_to_one(current_digest, sibling_digest);
                    result
                };
                leaf_index >>= 1;
                level = level + 1;
            }
            digests.insert((level, leaf_index), current_digest.clone());
        }
        PartialMT {
            log_max_capacity: level,
            digests,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::utils::helpers::generate_recproofs_leaves;

    use super::*;

    use rand::rngs::StdRng;
    use rand::seq::IteratorRandom;
    use rand::SeedableRng;

    use plonky2::hash::hash_types::RichField;
    use plonky2::hash::keccak::KeccakHash;
    use plonky2::hash::poseidon::PoseidonHash;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    fn mt_test_base<F: RichField, H: Hasher<F>>(ell: u8, log_subset_size: u8) {
        let size: u32 = 1 << ell;
        let subset_size: u32 = 1 << log_subset_size;

        let mut r: StdRng = StdRng::seed_from_u64(223);
        let subset_indices: HashSet<u32> =
            HashSet::from_iter((0..size).choose_multiple(&mut r, subset_size as usize));

        let leaves: HashMap<u32, Vec<F>> = generate_recproofs_leaves(4, &mut r, &subset_indices);

        let mut leaves_backup = leaves.clone();

        let mut mt = PartialMT::<F, H>::new(ell, &leaves);
        let root_digest = mt.get_digest();
        let mut proofs: Vec<MerkleProof<F, H>> = Vec::new();

        for (i, v) in subset_indices.iter().enumerate() {
            let proof = mt.prove(*v);
            proofs.push(proof);
            let result = PartialMT::verify(root_digest, *v, leaves.get(v).unwrap(), &proofs[i]);
            assert_eq!(result, true);
        }

        let update_leaf_index = subset_indices.iter().nth(0).unwrap().clone();
        let update_value = F::rand_vec(5);
        println!("Root digest: {:?}", mt.get_digest());
        println!("Update index: {}", update_leaf_index);
        println!("Current value: {:?}", leaves.get(&update_leaf_index));

        mt.update_tree(update_leaf_index, update_value.clone());
        let baseline = mt.get_digest();

        leaves_backup.insert(update_leaf_index, update_value);
        let mt = PartialMT::<F, H>::new(ell, &leaves_backup);
        assert!(baseline == mt.get_digest(), "Update failed.");

        let mut proofs: HashMap<u32, (Vec<F>, MerkleProof<F, H>)> = HashMap::new();
        for index in subset_indices {
            proofs.insert(
                index,
                (leaves.get(&index).unwrap().clone(), mt.prove(index)),
            );
        }

        let mt_partial = PartialMT::<F, H>::from_proofs(&proofs);
        println!(
            "Tree heights: {} {}",
            mt_partial.log_max_capacity, mt.log_max_capacity
        );
        assert!(
            mt_partial.log_max_capacity == mt.log_max_capacity,
            "Height mismatch after reconstruction."
        );
        assert!(
            mt_partial.get_digest() == mt.get_digest(),
            "Digest mismatch after reconstruction."
        );
    }

    #[test]
    fn mt_test_default() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type H1 = PoseidonHash;

        let ell: u8 = 10;
        let log_subset_size: u8 = 5;

        mt_test_base::<F, H1>(ell, log_subset_size);

        type H2 = KeccakHash<8>;
        mt_test_base::<F, H2>(ell, log_subset_size);
    }
}
