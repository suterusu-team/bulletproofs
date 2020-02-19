#![allow(non_snake_case)]
#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate rand;
use rand::thread_rng;

extern crate curve25519_dalek;
use curve25519_dalek::scalar::Scalar;

extern crate merlin;
use merlin::Transcript;

extern crate bulletproofs;
use bulletproofs::{BatchZetherProof, BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::RistrettoPoint;

static BATCH_SIZES: [usize; 7] = [3, 7, 15, 31, 63, 127, 255];

fn add_ciphertext(
    ctxt_1: &(RistrettoPoint, RistrettoPoint),
    ctxt_2: &(RistrettoPoint, RistrettoPoint),
) -> (RistrettoPoint, RistrettoPoint) {
    (ctxt_1.0 + ctxt_2.0, ctxt_1.1 + ctxt_2.1)
}

fn create_batched_zether(c: &mut Criterion) {
    let label = format!("Batched zether proof creation");
    c.bench_function_over_inputs(
        &label,
        move |b, &&m| {
            let mut balances = vec![]; // consists of sent and remaining balances
            let remaining_balance = 123u64;
            let mut initial_balance = remaining_balance;
            for _ in 0..m {
                initial_balance += 1111u64;
                balances.push(1111u64);
            }
            balances.push(remaining_balance);

            let pc_gens = PedersenGens::default();
            let bp_gens = BulletproofGens::new(64, m + 1);

            let mut blindings = vec![];
            let mut commitments = vec![];
            for i in 0..(m + 1) {
                blindings.push(Scalar::random(&mut thread_rng()));
                commitments.push(pc_gens.commit(Scalar::from(balances[i]), blindings[i]));
            }

            let sk = Scalar::random(&mut thread_rng());
            let g = pc_gens.B;

            let y = &sk * &g; // public key sender
            let mut receiver_keys = vec![];
            for _ in 0..m {
                receiver_keys.push(RistrettoPoint::random(&mut thread_rng()));
            }

            let random_encryption = Scalar::random(&mut thread_rng());
            let (Cl, Cr) = (
                &Scalar::from(initial_balance) * &g + &random_encryption * &y,
                &random_encryption * &g,
            );

            let blinding_factor = Scalar::random(&mut thread_rng());
            let mut enc_amounts_sender = vec![];
            let mut enc_amounts_receivers = vec![];

            for i in 0..m {
                enc_amounts_sender.push((
                    &Scalar::from(balances[i]) * &g + &blinding_factor * &y,
                    &blinding_factor * &g,
                ));
                enc_amounts_receivers.push((
                    &Scalar::from(balances[i]) * &g + &blinding_factor * receiver_keys[i],
                    &blinding_factor * &g,
                ));
            }

            let mut added_encrypted_amount = (Scalar::zero() * g, Scalar::zero() * g);
            for i in enc_amounts_sender.clone() {
                added_encrypted_amount = add_ciphertext(&added_encrypted_amount, &i)
            }

            let Cln = Cl - added_encrypted_amount.0;
            let Crn = Cr - added_encrypted_amount.1;

            b.iter(|| {
                // Each proof creation requires a clean transcript.
                let mut transcript = Transcript::new(b"AggregateRangeProofBenchmark");

                BatchZetherProof::prove_multiple(
                    &bp_gens,
                    &pc_gens,
                    &mut transcript,
                    &balances,
                    &blindings,
                    64,
                    &y,
                    &receiver_keys,
                    &(Cln, Crn),
                    enc_amounts_sender.clone(),
                    &sk,
                    &blinding_factor,
                )
                .expect("A real program could handle errors");
            })
        },
        &BATCH_SIZES,
    );
}

fn verify_batch_zether(c: &mut Criterion) {
    let label = format!("Batched zether proof verification");
    c.bench_function_over_inputs(
        &label,
        move |b, &&m| {
            let mut balances = vec![]; // consists of sent and remaining balances
            let remaining_balance = 123u64;
            let mut initial_balance = remaining_balance;
            for _ in 0..m {
                initial_balance += 1111u64;
                balances.push(1111u64);
            }
            balances.push(remaining_balance);

            let pc_gens = PedersenGens::default();
            let bp_gens = BulletproofGens::new(64, m + 1);

            let mut blindings = vec![];
            let mut commitments = vec![];
            for i in 0..(m + 1) {
                blindings.push(Scalar::random(&mut thread_rng()));
                commitments
                    .push((pc_gens.commit(Scalar::from(balances[i]), blindings[i])).compress());
            }

            let sk = Scalar::random(&mut thread_rng());
            let g = pc_gens.B;

            let y = &sk * &g; // public key sender
            let mut receiver_keys = vec![];
            for _ in 0..m {
                receiver_keys.push(RistrettoPoint::random(&mut thread_rng()));
            }

            let random_encryption = Scalar::random(&mut thread_rng());
            let (Cl, Cr) = (
                &Scalar::from(initial_balance) * &g + &random_encryption * &y,
                &random_encryption * &g,
            );

            let blinding_factor = Scalar::random(&mut thread_rng());
            let mut enc_amounts_sender = vec![];
            let mut enc_amounts_receivers = vec![];

            for i in 0..m {
                enc_amounts_sender.push((
                    &Scalar::from(balances[i]) * &g + &blinding_factor * &y,
                    &blinding_factor * &g,
                ));
                enc_amounts_receivers.push((
                    &Scalar::from(balances[i]) * &g + &blinding_factor * receiver_keys[i],
                    &blinding_factor * &g,
                ));
            }

            let mut added_encrypted_amount = (Scalar::zero() * g, Scalar::zero() * g);
            for i in enc_amounts_sender.clone() {
                added_encrypted_amount = add_ciphertext(&added_encrypted_amount, &i)
            }

            let Cln = Cl - added_encrypted_amount.0;
            let Crn = Cr - added_encrypted_amount.1;

            let mut transcript = Transcript::new(b"AggregateRangeProofBenchmark");

            let proof = BatchZetherProof::prove_multiple(
                &bp_gens,
                &pc_gens,
                &mut transcript,
                &balances,
                &blindings,
                64,
                &y,
                &receiver_keys,
                &(Cln, Crn),
                enc_amounts_sender.clone(),
                &sk,
                &blinding_factor,
            )
            .expect("A real program could handle errors");

            b.iter(|| {
                // Each proof creation requires a clean transcript.
                let mut transcript = Transcript::new(b"AggregateRangeProofBenchmark");

                proof.0.verify_multiple(
                    &bp_gens,
                    &pc_gens,
                    &mut transcript,
                    &commitments,
                    64,
                    &y,
                    &receiver_keys,
                    &(Cln, Crn),
                    enc_amounts_sender.clone(),
                    enc_amounts_receivers.clone(),
                )
            })
        },
        &BATCH_SIZES,
    );
}

criterion_group! {
    name = create_rp;
    config = Criterion::default().sample_size(10);
    targets =
    create_batched_zether,
}

criterion_group! {
    name = verify_rp;
    config = Criterion::default();
    targets =
    verify_batch_zether,
}

criterion_main!(create_rp, verify_rp);
