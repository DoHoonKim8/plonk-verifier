use ethereum_types::Address;
use halo2_curves::{bn256::{Bn256, Fq, Fr, G1Affine}, FieldExt};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{
        create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Circuit, Column,
        ConstraintSystem, Error, Fixed, Instance, ProvingKey, VerifyingKey,
    },
    poly::{
        commitment::{Params, ParamsProver},
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverGWC, VerifierGWC},
            strategy::AccumulatorStrategy,
        },
        Rotation, VerificationStrategy,
    },
    transcript::{TranscriptReadBuffer, TranscriptWriterBuffer},
};
use itertools::Itertools;
use plonk_verifier::{
    loader::evm::{encode_calldata, EvmLoader, ExecutorBuilder},
    pcs::kzg::{Gwc19, Kzg},
    system::halo2::{compile, transcript::evm::EvmTranscript, Config},
    verifier::{self, PlonkVerifier},
};
use rand::{rngs::OsRng, RngCore};
use std::rc::Rc;
use transcript::{
    HasherChip,
    maingate::{MainGateConfig, MainGate, RegionCtx, MainGateInstructions}
};
use poseidon::Spec;

type Plonk = verifier::Plonk<Kzg<Bn256, Gwc19>>;

#[derive(Clone)]
pub struct MerkleTreeCircuitConfig {
    pub config: MainGateConfig,
}

#[derive(Clone, Debug)]
pub struct MerkleTreeCircuit<F: FieldExt> {
    pub merkle_proof: Vec<Value<F>>,
    pub merkle_path: Vec<Value<F>>,
    pub leaf_node: Value<F>,
    pub hash_root: Value<F>,
}

impl<F: FieldExt> Circuit<F> for MerkleTreeCircuit<F> {
    type Config = MerkleTreeCircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn configure(meta: &mut transcript::halo2::plonk::ConstraintSystem<F>) -> Self::Config {
        let config = MainGate::configure(meta);
        MerkleTreeCircuitConfig { config }
    }

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl transcript::halo2::circuit::Layouter<F>,
    ) -> Result<(), transcript::halo2::plonk::Error> {
        let config = config.config;
        // TODO: Check the size of merkle_path and merkle_proof is equal
        layouter.assign_region(
            || "",
            |region| {
                let mut ctx = RegionCtx::new(region, 0);
                let spec = Spec::<F, 3, 2>::new(8, 57);
                let mut hasher_chip = HasherChip::<F, 0, 0, 3, 2>::new(&mut ctx, &spec, &config)?;
                let main_gate = hasher_chip.main_gate();

                let mut hash_root = main_gate.assign_value(&mut ctx, self.leaf_node)?;

                for (id, hash_value) in self.merkle_proof.iter().enumerate() {
                    let select = main_gate.assign_value(&mut ctx, self.merkle_path[id])?;
                    let hash_cell = main_gate.assign_value(&mut ctx, *hash_value)?;

                    let left_child = main_gate.select(&mut ctx, &hash_root, &hash_cell, &select)?;
                    let right_child =
                        main_gate.select(&mut ctx, &hash_cell, &hash_root, &select)?;

                    hasher_chip.update(&[left_child, right_child]);
                    hash_root = hasher_chip.hash(&mut ctx)?;
                }

                let root_cell = main_gate.assign_value(&mut ctx, self.hash_root)?;

                main_gate.assert_equal(&mut ctx, &hash_root, &root_cell)
            },
        )?;
        Ok(())
    }
}

fn gen_srs(k: u32) -> ParamsKZG<Bn256> {
    ParamsKZG::<Bn256>::setup(k, OsRng)
}

fn gen_pk<C: Circuit<Fr>>(params: &ParamsKZG<Bn256>, circuit: &C) -> ProvingKey<G1Affine> {
    let vk = keygen_vk(params, circuit).unwrap();
    keygen_pk(params, vk, circuit).unwrap()
}

fn gen_proof<C: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
) -> Vec<u8> {
    MockProver::run(params.k(), &circuit, instances.clone())
        .unwrap()
        .assert_satisfied();

    let instances = instances
        .iter()
        .map(|instances| instances.as_slice())
        .collect_vec();
    let proof = {
        let mut transcript = TranscriptWriterBuffer::<_, G1Affine, _>::init(Vec::new());
        create_proof::<KZGCommitmentScheme<Bn256>, ProverGWC<_>, _, _, EvmTranscript<_, _, _, _>, _>(
            params,
            pk,
            &[circuit],
            &[instances.as_slice()],
            OsRng,
            &mut transcript,
        )
        .unwrap();
        transcript.finalize()
    };

    let accept = {
        let mut transcript = TranscriptReadBuffer::<_, G1Affine, _>::init(proof.as_slice());
        VerificationStrategy::<_, VerifierGWC<_>>::finalize(
            verify_proof::<_, VerifierGWC<_>, _, EvmTranscript<_, _, _, _>, _>(
                params.verifier_params(),
                pk.get_vk(),
                AccumulatorStrategy::new(params.verifier_params()),
                &[instances.as_slice()],
                &mut transcript,
            )
            .unwrap(),
        )
    };
    assert!(accept);

    proof
}

fn gen_evm_verifier(
    params: &ParamsKZG<Bn256>,
    vk: &VerifyingKey<G1Affine>,
    num_instance: Vec<usize>,
) -> Vec<u8> {
    let svk = params.get_g()[0].into();
    let dk = (params.g2(), params.s_g2()).into();
    let protocol = compile(
        params,
        vk,
        Config::kzg().with_num_instance(num_instance.clone()),
    );

    let loader = EvmLoader::new::<Fq, Fr>();
    let protocol = protocol.loaded(&loader);
    let mut transcript = EvmTranscript::<_, Rc<EvmLoader>, _, _>::new(&loader);

    let instances = transcript.load_instances(num_instance);
    let proof = Plonk::read_proof(&svk, &protocol, &instances, &mut transcript).unwrap();
    Plonk::verify(&svk, &dk, &protocol, &instances, &proof).unwrap();

    loader.deployment_code()
}

fn evm_verify(deployment_code: Vec<u8>, instances: Vec<Vec<Fr>>, proof: Vec<u8>) {
    let calldata = encode_calldata(&instances, &proof);
    let success = {
        let mut evm = ExecutorBuilder::default()
            .with_gas_limit(u64::MAX.into())
            .build();

        let caller = Address::from_low_u64_be(0xfe);
        let verifier = evm
            .deploy(caller, deployment_code.into(), 0.into())
            .address
            .unwrap();
        let result = evm.call_raw(caller, verifier, calldata.into(), 0.into());

        dbg!(result.gas_used);

        !result.reverted
    };
    assert!(success);
}

fn main() {
    let params = gen_srs(10);

    let mut leaf = Fr::from(123);
    let mut merkle_proof = Vec::new();
    let mut hasher = poseidon::Poseidon::<Fr, 3, 2>::new(8, 57);

    for value in 0..1 {
        hasher.update(&[leaf, Fr::from(value)]);
        leaf = hasher.squeeze();
        merkle_proof.push(Fr::from(value));
    }

    let circuit = MerkleTreeCircuit {
        leaf_node: Value::known(Fr::from(123)),
        merkle_path: (0..1).map(|_| Value::known(Fr::from(1))).collect(),
        hash_root: Value::known(leaf),
        merkle_proof: merkle_proof.iter().map(|v| Value::known(*v)).collect(),
    };
    let pk = gen_pk(&params, &circuit);
    let deployment_code = gen_evm_verifier(&params, pk.get_vk(), vec![]);

    let proof = gen_proof(&params, &pk, circuit.clone(), vec![vec![]]);
    evm_verify(deployment_code, vec![vec![]], proof);
}
