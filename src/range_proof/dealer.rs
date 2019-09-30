//! The `dealer` module contains the API for the dealer state while the dealer is
//! engaging in an aggregated multiparty computation protocol.
//!
//! For more explanation of how the `dealer`, `party`, and `messages` modules orchestrate the protocol execution, see
//! [the API for the aggregated multiparty computation protocol](../aggregation/index.html#api-for-the-aggregated-multiparty-computation-protocol).

use core::iter;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

use errors::MPCError;
use generators::{BulletproofGens, PedersenGens};
use inner_product_proof;
use range_proof::{RangeProof, ZetherProof};
use transcript::TranscriptProtocol;

use rand;
use util;

use super::messages::*;

/// Used to construct a dealer for the aggregated rangeproof MPC protocol.
pub struct Dealer {}

impl Dealer {
    /// Creates a new dealer coordinating `m` parties proving `n`-bit ranges.
    pub fn new<'a, 'b>(
        bp_gens: &'b BulletproofGens,
        pc_gens: &'b PedersenGens,
        transcript: &'a mut Transcript,
        n: usize,
        m: usize,
    ) -> Result<DealerAwaitingBitCommitments<'a, 'b>, MPCError> {
        if !(n == 8 || n == 16 || n == 32 || n == 64) {
            return Err(MPCError::InvalidBitsize);
        }
        if !m.is_power_of_two() {
            return Err(MPCError::InvalidAggregation);
        }
        if bp_gens.gens_capacity < n {
            return Err(MPCError::InvalidGeneratorsLength);
        }
        if bp_gens.party_capacity < m {
            return Err(MPCError::InvalidGeneratorsLength);
        }

        // At the end of the protocol, the dealer will attempt to
        // verify the proof, and if it fails, determine which party's
        // shares were invalid.
        //
        // However, verifying the proof requires either knowledge of
        // all of the challenges, or a copy of the initial transcript
        // state.
        //
        // The dealer has all of the challenges, but using them for
        // verification would require duplicating the verification
        // logic.  Instead, we keep a copy of the initial transcript
        // state.
        let initial_transcript = transcript.clone();

        transcript.rangeproof_domain_sep(n as u64, m as u64);

        Ok(DealerAwaitingBitCommitments {
            bp_gens,
            pc_gens,
            transcript,
            initial_transcript,
            n,
            m,
        })
    }
}

/// A dealer waiting for the parties to send their [`BitCommitment`]s.
pub struct DealerAwaitingBitCommitments<'a, 'b> {
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    transcript: &'a mut Transcript,
    /// The dealer keeps a copy of the initial transcript state, so
    /// that it can attempt to verify the aggregated proof at the end.
    initial_transcript: Transcript,
    n: usize,
    m: usize,
}

impl<'a, 'b> DealerAwaitingBitCommitments<'a, 'b> {
    /// Receive each party's [`BitCommitment`]s and compute the [`BitChallenge`].
    pub fn receive_bit_commitments(
        self,
        bit_commitments: Vec<BitCommitment>,
    ) -> Result<(DealerAwaitingPolyCommitments<'a, 'b>, BitChallenge), MPCError> {
        if self.m != bit_commitments.len() {
            return Err(MPCError::WrongNumBitCommitments);
        }

        // Commit each V_j individually
        for vc in bit_commitments.iter() {
            self.transcript.append_point(b"V", &vc.V_j);
        }

        // Commit aggregated A_j, S_j
        let A: RistrettoPoint = bit_commitments.iter().map(|vc| vc.A_j).sum();
        self.transcript.append_point(b"A", &A.compress());

        let S: RistrettoPoint = bit_commitments.iter().map(|vc| vc.S_j).sum();
        self.transcript.append_point(b"S", &S.compress());

        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");
        let bit_challenge = BitChallenge { y, z };

        Ok((
            DealerAwaitingPolyCommitments {
                n: self.n,
                m: self.m,
                transcript: self.transcript,
                initial_transcript: self.initial_transcript,
                bp_gens: self.bp_gens,
                pc_gens: self.pc_gens,
                bit_challenge,
                bit_commitments,
                A,
                S,
            },
            bit_challenge,
        ))
    }
}

/// A dealer which has sent the [`BitChallenge`] to the parties and
/// is waiting for their [`PolyCommitment`]s.
pub struct DealerAwaitingPolyCommitments<'a, 'b> {
    n: usize,
    m: usize,
    transcript: &'a mut Transcript,
    initial_transcript: Transcript,
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    bit_challenge: BitChallenge,
    bit_commitments: Vec<BitCommitment>,
    /// Aggregated commitment to the parties' bits
    A: RistrettoPoint,
    /// Aggregated commitment to the parties' bit blindings
    S: RistrettoPoint,
}

impl<'a, 'b> DealerAwaitingPolyCommitments<'a, 'b> {
    /// Receive [`PolyCommitment`]s from the parties and compute the
    /// [`PolyChallenge`].
    pub fn receive_poly_commitments(
        self,
        poly_commitments: Vec<PolyCommitment>,
    ) -> Result<(DealerAwaitingProofShares<'a, 'b>, PolyChallenge), MPCError> {
        if self.m != poly_commitments.len() {
            return Err(MPCError::WrongNumPolyCommitments);
        }

        // Commit sums of T_1_j's and T_2_j's
        let T_1: RistrettoPoint = poly_commitments.iter().map(|pc| pc.T_1_j).sum();
        let T_2: RistrettoPoint = poly_commitments.iter().map(|pc| pc.T_2_j).sum();

        self.transcript.append_point(b"T_1", &T_1.compress());
        self.transcript.append_point(b"T_2", &T_2.compress());

        let x = self.transcript.challenge_scalar(b"x");
        let poly_challenge = PolyChallenge { x };

        Ok((
            DealerAwaitingProofShares {
                n: self.n,
                m: self.m,
                transcript: self.transcript,
                initial_transcript: self.initial_transcript,
                bp_gens: self.bp_gens,
                pc_gens: self.pc_gens,
                bit_challenge: self.bit_challenge,
                bit_commitments: self.bit_commitments,
                A: self.A,
                S: self.S,
                poly_challenge,
                poly_commitments,
                T_1,
                T_2,
            },
            poly_challenge,
        ))
    }
}

/// A dealer which has sent the [`PolyChallenge`] to the parties and
/// is waiting to aggregate their [`ProofShare`]s into a
/// [`RangeProof`].
pub struct DealerAwaitingProofShares<'a, 'b> {
    n: usize,
    m: usize,
    transcript: &'a mut Transcript,
    initial_transcript: Transcript,
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    bit_challenge: BitChallenge,
    bit_commitments: Vec<BitCommitment>,
    poly_challenge: PolyChallenge,
    poly_commitments: Vec<PolyCommitment>,
    A: RistrettoPoint,
    S: RistrettoPoint,
    T_1: RistrettoPoint,
    T_2: RistrettoPoint,
}

impl<'a, 'b> DealerAwaitingProofShares<'a, 'b> {
    /// Assembles proof shares into an `RangeProof`.
    ///
    /// Used as a helper function by `receive_trusted_shares` (which
    /// just hands back the result) and `receive_shares` (which
    /// validates the proof shares.
    fn assemble_shares(&mut self, proof_shares: &[ProofShare]) -> Result<RangeProof, MPCError> {
        if self.m != proof_shares.len() {
            return Err(MPCError::WrongNumProofShares);
        }

        let t_x: Scalar = proof_shares.iter().map(|ps| ps.t_x).sum();
        let t_x_blinding: Scalar = proof_shares.iter().map(|ps| ps.t_x_blinding).sum();
        let e_blinding: Scalar = proof_shares.iter().map(|ps| ps.e_blinding).sum();

        self.transcript.append_scalar(b"t_x", &t_x);
        self.transcript
            .append_scalar(b"t_x_blinding", &t_x_blinding);
        self.transcript.append_scalar(b"e_blinding", &e_blinding);

        // Get a challenge value to combine statements for the IPP
        let w = self.transcript.challenge_scalar(b"w");
        let Q = w * self.pc_gens.B;

        let G_factors: Vec<Scalar> = iter::repeat(Scalar::one()).take(self.n * self.m).collect();
        let H_factors: Vec<Scalar> = util::exp_iter(self.bit_challenge.y.invert())
            .take(self.n * self.m)
            .collect();

        let l_vec: Vec<Scalar> = proof_shares
            .iter()
            .flat_map(|ps| ps.l_vec.clone().into_iter())
            .collect();
        let r_vec: Vec<Scalar> = proof_shares
            .iter()
            .flat_map(|ps| ps.r_vec.clone().into_iter())
            .collect();

        let ipp_proof = inner_product_proof::InnerProductProof::create(
            self.transcript,
            &Q,
            &G_factors,
            &H_factors,
            self.bp_gens.G(self.n, self.m).cloned().collect(),
            self.bp_gens.H(self.n, self.m).cloned().collect(),
            l_vec,
            r_vec,
        );

        Ok(RangeProof {
            A: self.A.compress(),
            S: self.S.compress(),
            T_1: self.T_1.compress(),
            T_2: self.T_2.compress(),
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        })
    }

    /// Assemble the final aggregated [`RangeProof`] from the given
    /// `proof_shares`, then validate the proof to ensure that all
    /// `ProofShare`s were well-formed.
    ///
    /// If the aggregated proof fails to validate, this function
    /// audits the submitted shares to determine which shares were
    /// invalid.  This information is returned as part of the
    /// [`MPCError`].
    ///
    /// If the proof shares are known to be trusted, for instance when
    /// performing local aggregation,
    /// [`receive_trusted_shares`](DealerAwaitingProofShares::receive_trusted_shares)
    /// saves time by skipping verification of the aggregated proof.
    pub fn receive_shares(mut self, proof_shares: &[ProofShare]) -> Result<RangeProof, MPCError> {
        let proof = self.assemble_shares(proof_shares)?;

        let Vs: Vec<_> = self.bit_commitments.iter().map(|vc| vc.V_j).collect();

        // See comment in `Dealer::new` for why we use `initial_transcript`
        let transcript = &mut self.initial_transcript;
        if proof
            .verify_multiple(self.bp_gens, self.pc_gens, transcript, &Vs, self.n)
            .is_ok()
        {
            Ok(proof)
        } else {
            // Proof verification failed. Now audit the parties:
            let mut bad_shares = Vec::new();
            for j in 0..self.m {
                match proof_shares[j].audit_share(
                    &self.bp_gens,
                    &self.pc_gens,
                    j,
                    &self.bit_commitments[j],
                    &self.bit_challenge,
                    &self.poly_commitments[j],
                    &self.poly_challenge,
                ) {
                    Ok(_) => {}
                    Err(_) => bad_shares.push(j),
                }
            }
            Err(MPCError::MalformedProofShares { bad_shares })
        }
    }

    /// Assemble the final aggregated [`RangeProof`] from the given
    /// `proof_shares`, but skip validation of the proof.
    ///
    /// ## WARNING
    ///
    /// This function does **NOT** validate the proof shares.  It is
    /// suitable for creating aggregated proofs when all parties are
    /// known by the dealer to be honest (for instance, when there's
    /// only one party playing all roles).
    ///
    /// Otherwise, use
    /// [`receive_shares`](DealerAwaitingProofShares::receive_shares),
    /// which validates that all shares are well-formed, or else
    /// detects which party(ies) submitted malformed shares.
    pub fn receive_trusted_shares(
        mut self,
        proof_shares: &[ProofShare],
    ) -> Result<RangeProof, MPCError> {
        self.assemble_shares(proof_shares)
    }
    /// Assemble the final aggregated [`RangeProof`] from the given
    /// `proof_shares`, but skip validation of the proof. Furthermore
    /// it takes the remaining ZetherProof components to generate
    /// the complete ZetherProof (combining the Bulletproof and the 
    /// sigma protocol).
    ///
    /// ## WARNING
    ///
    /// This function does **NOT** validate the proof shares.  It is
    /// suitable for creating aggregated proofs when all parties are
    /// known by the dealer to be honest (for instance, when there's
    /// only one party playing all roles).
    pub fn receive_shares_and_generate_zether(
        mut self, 
        sent_balance: &Scalar, 
        remaining_balance: &Scalar,

        proof_shares: &[ProofShare],
        pk_sender: &RistrettoPoint, 
        pk_receiver: &RistrettoPoint, 
        enc_balance_after_transfer: (&RistrettoPoint, &RistrettoPoint), 
        enc_amount_sender: (&RistrettoPoint, &RistrettoPoint),
        sk_sender: &Scalar, 
        comm_rnd: &Scalar,

    ) -> Result<ZetherProof, MPCError> {
        let range_proof = self.assemble_shares(proof_shares)?;
        let mut rng = rand::thread_rng();

        let pc_gens = self.pc_gens;
        let base_point = pc_gens.B;
        
        let z = self.bit_challenge.z;
        let z_square = z * z;
        let z_cube = &z_square * z;

        // Blinding factors
        let sk_hiding = Scalar::random(&mut rng);
        let random_hiding = Scalar::random(&mut rng);
        let balance_hiding = Scalar::random(&mut rng);

        // Commitment to blinding factors (or announcements)
        let ann_y = &sk_hiding * base_point;
        let ann_D = &random_hiding * base_point; // Different from the original paper, they have a typo. (Their equation does not validate)
        let ann_b = &balance_hiding * base_point + sk_hiding * (z_square * enc_amount_sender.1 +  z_cube * enc_balance_after_transfer.1);
        let ann_y_ = &random_hiding * (pk_sender - pk_receiver); // in high doubt that this is correct
        let ann_t = sk_hiding * (z_cube * enc_balance_after_transfer.1 + z_square * enc_amount_sender.1);

        let challenge_sigma = self.transcript.challenge_scalar(b"challenge_sigma");

        // Responses of the sigma protocol
        let res_sk = sk_hiding + challenge_sigma * sk_sender;
        let res_r = random_hiding + challenge_sigma * comm_rnd;
        let res_b = balance_hiding + challenge_sigma *(sent_balance * (z_square) + remaining_balance * (z_cube));

        Ok(range_proof.to_ZetherProof(ann_y, ann_D, ann_b, ann_y_, ann_t, res_sk, res_r, res_b))
    }
}
