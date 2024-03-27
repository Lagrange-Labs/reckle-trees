use plonky2::{
    field::extension::Extendable,
    hash::hash_types::{HashOutTarget, RichField},
    iop::witness::{PartialWitness, WitnessWrite},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WireInformation<const D: usize> {
    pub(crate) data_target: Vec<HashOutTarget>,
}
impl<const D: usize> WireInformation<D> {
    pub fn new(data_target: &[HashOutTarget]) -> Self {
        Self {
            data_target: data_target.to_vec(),
        }
    }
    pub fn compute_pw<F>(&self, data_target: &Vec<Vec<F>>) -> PartialWitness<F>
    where
        F: RichField + Extendable<D>,
    {
        let mut pw: PartialWitness<F> = PartialWitness::new();

        for i in 0..data_target.len() {
            pw.set_target_arr(&self.data_target[i].elements, &data_target[i]);
        }
        pw
    }
}
