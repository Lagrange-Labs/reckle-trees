use std::collections::HashMap;
use std::marker::PhantomData;

use plonky2_bn254::curves::{BN254GateSerializer, BN254GeneratorSerializer};

use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_data::{CommonCircuitData, ProverCircuitData, VerifierCircuitData};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig};

use crate::bls::binary_circuits::{
    compact_circuit_setup, internal_circuit_setup, leaf_circuit_setup,
};
use crate::bls::wire_information::{
    CompactWireInformation, InternalWireInformation, LeafWireInformation,
};

#[allow(non_camel_case_types)]
pub struct SNARK_PP<const Q: usize, F, C, const D: usize>
where
    C: GenericConfig<D, F = F>,
    F: RichField + Extendable<D>,
    [(); 1 << Q]:,
{
    pub log_max_capacity: u8,
    pub compaction_level: u8,

    pub leaf_wire_information: LeafWireInformation<D>,
    pub common_leaf: CommonCircuitData<F, D>,
    pub prover_leaf: ProverCircuitData<F, C, D>,
    pub verifier_leaf: VerifierCircuitData<F, C, D>,

    pub internal_wire_information: Vec<InternalWireInformation<D>>,
    pub common_internal: Vec<CommonCircuitData<F, D>>,
    pub prover_internal: Vec<ProverCircuitData<F, C, D>>,
    pub verifier_internal: Vec<VerifierCircuitData<F, C, D>>,

    pub wire_information_compact: Vec<CompactWireInformation<D>>,
    pub common_compact: Vec<CommonCircuitData<F, D>>,
    pub prover_compact: Vec<ProverCircuitData<F, C, D>>,
    pub verifier_compact: Vec<VerifierCircuitData<F, C, D>>,
}
impl<const Q: usize, F, C, const D: usize> SNARK_PP<Q, F, C, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
    [(); 1 << Q]:,
{
    pub fn setup(log_max_capacity: u8) -> Self {
        assert!(Q == 1);
        let compaction_level = 2 as u8;
        let min_degree_bits_hashmap: HashMap<u8, usize> = HashMap::new();

        let (leaf_wire_information, common_leaf, prover_leaf, verifier_leaf) =
            leaf_circuit_setup::<F, C, D>(min_degree_bits_hashmap.get(&(1)));

        let mut prev_common = common_leaf.clone();
        let mut prev_hash = verifier_leaf.verifier_only.circuit_digest.clone();

        let mut internal_wire_information: Vec<InternalWireInformation<D>> = Vec::new();
        let mut common_internal: Vec<CommonCircuitData<F, D>> = Vec::new();
        let mut prover_internal: Vec<ProverCircuitData<F, C, D>> = Vec::new();
        let mut verifier_internal: Vec<VerifierCircuitData<F, C, D>> = Vec::new();

        for i in (Q as u8) + 1..=log_max_capacity {
            let (wire_information, common, prover, verifier) = internal_circuit_setup::<F, C, C, D>(
                &prev_common,
                prev_hash,
                min_degree_bits_hashmap.get(&i),
            );
            prev_common = common.clone();
            prev_hash = verifier.verifier_only.circuit_digest.clone();
            internal_wire_information.push(wire_information);
            common_internal.push(common);
            prover_internal.push(prover);
            verifier_internal.push(verifier);
        }

        let mut wire_information_compact: Vec<CompactWireInformation<D>> = Vec::new();
        let mut common_compact: Vec<CommonCircuitData<F, D>> = Vec::new();
        let mut prover_compact: Vec<ProverCircuitData<F, C, D>> = Vec::new();
        let mut verifier_compact: Vec<VerifierCircuitData<F, C, D>> = Vec::new();

        for _ in 0..compaction_level {
            let (wire_information, common, prover, verifier) =
                compact_circuit_setup::<F, C, C, D>(&prev_common, prev_hash, None);

            prev_common = common.clone();
            prev_hash = verifier.verifier_only.circuit_digest.clone();

            wire_information_compact.push(wire_information);
            common_compact.push(common);
            prover_compact.push(prover);
            verifier_compact.push(verifier);
        }
        Self {
            log_max_capacity,
            compaction_level,

            leaf_wire_information,
            common_leaf,
            prover_leaf,
            verifier_leaf,

            internal_wire_information,
            common_internal,
            prover_internal,
            verifier_internal,

            wire_information_compact,
            common_compact,
            prover_compact,
            verifier_compact,
        }
    }

    pub fn get_verifier(&self) -> &VerifierCircuitData<F, C, D> {
        return &self.verifier_compact[(self.compaction_level - 1) as usize];
    }

    pub fn size_by_level(&self) {
        let factor_1024 = 1024.0;
        let gate_serializer = BN254GateSerializer {};
        let gen_serializer = BN254GeneratorSerializer::<C, D> {
            _phantom: PhantomData,
        };

        let common_leaf_size =
            self.common_leaf.to_bytes(&gate_serializer).unwrap().len() as f64 / factor_1024;
        let prover_leaf_size = self
            .prover_leaf
            .to_bytes(&gate_serializer, &gen_serializer)
            .unwrap()
            .len() as f64
            / factor_1024
            / factor_1024;
        let verifier_leaf_size =
            self.verifier_leaf.to_bytes(&gate_serializer).unwrap().len() as f64 / factor_1024;

        println!(
            "==== {}/{} common data: {:>4.2} KiB, prover data: {:>6.2} MiB, verifier data: {:>4.2} KiB",
            1, self.log_max_capacity, common_leaf_size, prover_leaf_size, verifier_leaf_size
        );

        for i in (Q as u8 + 1)..=self.log_max_capacity {
            let internal_config_index = i as usize - (Q + 1);
            let common_internal_size = self.common_internal[internal_config_index]
                .to_bytes(&gate_serializer)
                .unwrap()
                .len() as f64
                / factor_1024;
            let prover_internal_size = self.prover_internal[internal_config_index]
                .to_bytes(&gate_serializer, &gen_serializer)
                .unwrap()
                .len() as f64
                / factor_1024
                / factor_1024;
            let verifier_internal_size = self.verifier_internal[internal_config_index]
                .to_bytes(&gate_serializer)
                .unwrap()
                .len() as f64
                / factor_1024;

            println!(
                    "==== {}/{} common data: {:>4.2} KiB, prover data: {:>6.2} MiB, verifier data: {:>4.2} KiB",
                    i,
                    self.log_max_capacity,
                    common_internal_size,
                    prover_internal_size,
                    verifier_internal_size
                );
        }

        for i in 0..self.compaction_level as usize {
            let common_compact_size = self.common_compact[i]
                .to_bytes(&gate_serializer)
                .unwrap()
                .len() as f64
                / factor_1024;
            let prover_compact_size = self.prover_compact[i]
                .to_bytes(&gate_serializer, &gen_serializer)
                .unwrap()
                .len() as f64
                / factor_1024
                / factor_1024;
            let verifier_compact_size = self.verifier_compact[i]
                .to_bytes(&gate_serializer)
                .unwrap()
                .len() as f64
                / factor_1024;
            println!(
                "==== {}/{} common data: {:>4.2} KiB, prover data: {:>6.2} MiB, verifier data: {:>4.2} KiB",
                self.log_max_capacity as usize + i + 1,
                self.log_max_capacity,
                common_compact_size,
                prover_compact_size,
                verifier_compact_size
            )
        }
    }
}
