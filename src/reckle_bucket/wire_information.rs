use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::{HashOut, HashOutTarget, RichField};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};

use crate::reckle_std;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct LeafWireInformation<const Q: usize, const D: usize>
where
    [(); 1 << Q]:,
{
    pub(crate) merkle_targets_q: [HashOutTarget; 1 << Q],
    pub(crate) canonical_targets_q: [HashOutTarget; 1 << Q],
}
impl<const Q: usize, const D: usize> LeafWireInformation<Q, D>
where
    [(); 1 << Q]:,
{
    pub fn new(merkle_targets_q: &[HashOutTarget], canonical_targets_q: &[HashOutTarget]) -> Self {
        Self {
            merkle_targets_q: merkle_targets_q
                .try_into()
                .expect("wire_information: slice with incorrect length"),
            canonical_targets_q: canonical_targets_q
                .try_into()
                .expect("wire_information: slice with incorrect length"),
        }
    }
    pub fn compute_pw<F>(
        &self,
        merkle_targets: &[HashOut<F>],
        canonical_targets: &[HashOut<F>],
    ) -> PartialWitness<F>
    where
        F: RichField + Extendable<D>,
    {
        let bucket_size = 1 << Q;
        let mut pw: PartialWitness<F> = PartialWitness::new();
        assert!(merkle_targets.len() == bucket_size);
        assert!(canonical_targets.len() == bucket_size);
        for i in 0..bucket_size {
            pw.set_hash_target(self.merkle_targets_q[i], merkle_targets[i]);
            pw.set_hash_target(self.canonical_targets_q[i], canonical_targets[i]);
        }
        return pw;
    }
}

pub struct InternalWireInformation<const D: usize>(
    pub reckle_std::wire_information::InternalWireInformation<D>,
);

pub struct CompactWireInformation<const D: usize>(
    pub reckle_std::wire_information::CompactWireInformation<D>,
);
