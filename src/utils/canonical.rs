use std::collections::HashMap;
use std::collections::HashSet;

use plonky2::hash::hash_types::RichField;
use plonky2::plonk::config::GenericHashOut;
use plonky2::plonk::config::Hasher;

#[derive(Debug, Clone, PartialEq)]
pub struct CanonicalTree<F: RichField, H: Hasher<F>> {
    pub log_max_capacity: u8, // Indexed from 0
    pub digests: HashMap<(u8, u32), H::Hash>,
}

impl<F: RichField, H: Hasher<F>> CanonicalTree<F, H> {
    pub fn default() -> H::Hash {
        H::Hash::from_bytes(&vec![0; H::HASH_SIZE])
    }

    pub fn new(log_max_capacity: u8, subset_leaves: &HashMap<u32, Vec<F>>) -> Self {
        let mut indices: HashSet<u32> = HashSet::new();
        let mut digests: HashMap<(u8, u32), H::Hash> = HashMap::new();

        for (index, value) in subset_leaves {
            indices.insert(index.clone() >> 1);
            digests.insert((0, index.clone()), H::hash_or_noop(&value));
        }

        for i in 1..log_max_capacity + 1 as u8 {
            for j in &indices {
                let key1: (u8, u32) = (i - 1, 2 * (*j));
                let key2: (u8, u32) = (i - 1, 2 * (*j) + 1);
                let key = (i, *j);

                let (left_value, left_flag) = match digests.get(&key1) {
                    Some(value) => (value.clone(), 1),
                    None => (Self::default(), 0),
                };
                let (right_value, right_flag) = match digests.get(&key2) {
                    Some(value) => (value.clone(), 1),
                    None => (Self::default(), 0),
                };

                let parent;
                if left_flag == 1 && right_flag == 1 {
                    parent = H::two_to_one(left_value, right_value);
                } else if left_flag == 1 {
                    parent = left_value;
                } else {
                    parent = right_value;
                }
                digests.insert(key, parent);
            }
            indices = HashSet::from_iter(indices.into_iter().map(|i| i >> 1));
        }
        Self {
            log_max_capacity,
            digests,
        }
    }
    pub fn get_digest(&self) -> H::Hash {
        self.digests
            .get(&(self.log_max_capacity, 0))
            .unwrap()
            .clone()
    }

    pub fn update_tree(&mut self, leaf_index: u32, updated_value: Vec<F>) {
        let default_hash = H::Hash::from_bytes(&vec![0; H::HASH_SIZE]);
        let mut leaf_index = leaf_index;

        self.digests
            .insert((0, leaf_index.clone()), H::hash_or_noop(&updated_value));

        for i in 1..self.log_max_capacity + 1 as u8 {
            leaf_index = leaf_index >> 1;

            let key1: (u8, u32) = (i - 1, 2 * leaf_index);
            let key2: (u8, u32) = (i - 1, 2 * leaf_index + 1);
            let key = (i, leaf_index);

            let (left_value, left_flag) = match self.digests.get(&key1) {
                Some(value) => (value.clone(), 1),
                None => (default_hash.clone(), 0),
            };
            let (right_value, right_flag) = match self.digests.get(&key2) {
                Some(value) => (value.clone(), 1),
                None => (default_hash.clone(), 0),
            };

            let parent;
            if left_flag == 1 && right_flag == 1 {
                parent = H::two_to_one(left_value, right_value);
            } else if left_flag == 1 {
                parent = left_value;
            } else {
                parent = right_value;
            }
            self.digests.insert(key, parent);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::utils::mt_binary::PartialMT;

    use super::*;
    use plonky2::hash::poseidon::PoseidonHash;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use rand::seq::IteratorRandom;

    fn ct_test_base<F: RichField, H: Hasher<F>>(ell: u8) {
        let size: u32 = 1 << ell;
        let subset_size: u32 = 1 << ell;

        let subset_indices: HashSet<u32> = HashSet::from_iter(
            (0..size).choose_multiple(&mut rand::thread_rng(), subset_size as usize),
        );

        let leaves: HashMap<u32, Vec<F>> = subset_indices
            .clone()
            .into_iter()
            .map(|i| (i as u32, F::rand_vec(5)))
            .collect::<HashMap<_, _>>();

        let mt = PartialMT::<F, H>::new(ell, &leaves);
        let ct = CanonicalTree::<F, H>::new(ell, &leaves);

        let root_merkle_digest = mt.get_digest();
        let root_canonical_digest = ct.get_digest();

        assert!(
            root_merkle_digest == root_canonical_digest,
            "Digest mismatch after reconstruction."
        );
    }

    #[test]
    fn ct_test_1() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type H1 = PoseidonHash;

        let ell: u8 = 10;
        ct_test_base::<F, H1>(ell);
    }
}
