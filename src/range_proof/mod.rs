#![allow(non_snake_case)]
#![doc(include = "../../docs/range-proof-protocol.md")]

extern crate alloc;
#[cfg(feature = "std")]
extern crate rand;

#[cfg(feature = "std")]
use self::rand::thread_rng;
use alloc::vec::Vec;

use core::iter;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{IsIdentity, VartimeMultiscalarMul};
use merlin::Transcript;

use crate::errors::ProofError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::inner_product_proof::InnerProductProof;
use crate::transcript::TranscriptProtocol;
use crate::util;

use rand_core::{CryptoRng, RngCore};
use serde::de::Visitor;
use serde::{self, Deserialize, Deserializer, Serialize, Serializer};

// Modules for MPC protocol

pub mod batch_proof;
pub mod dealer;
pub mod messages;
pub mod party;

use self::batch_proof::BatchZetherProof;

/// The `RangeProof` struct represents a proof that one or more values
/// are in a range.
///
/// The `RangeProof` struct contains functions for creating and
/// verifying aggregated range proofs.  The single-value case is
/// implemented as a special case of aggregated range proofs.
///
/// The bitsize of the range, as well as the list of commitments to
/// the values, are not included in the proof, and must be known to
/// the verifier.
///
/// This implementation requires that both the bitsize `n` and the
/// aggregation size `m` be powers of two, so that `n = 8, 16, 32, 64`
/// and `m = 1, 2, 4, 8, 16, ...`.  Note that the aggregation size is
/// not given as an explicit parameter, but is determined by the
/// number of values or commitments passed to the prover or verifier.
///
/// # Note
///
/// For proving, these functions run the multiparty aggregation
/// protocol locally.  That API is exposed in the [`aggregation`](::range_proof_mpc)
/// module and can be used to perform online aggregation between
/// parties without revealing secret values to each other.
#[derive(Clone, Debug)]
pub struct RangeProof {
    /// Commitment to the bits of the value
    A: CompressedRistretto,
    /// Commitment to the blinding factors
    S: CompressedRistretto,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    T_1: CompressedRistretto,
    /// Commitment to the \\(t_2\\) coefficient of \\( t(x) \\)
    T_2: CompressedRistretto,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\(t(x)\\)
    t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the inner-product arguments
    e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    ipp_proof: InnerProductProof,
}

impl RangeProof {
    /// Create a rangeproof for a given pair of value `v` and
    /// blinding scalar `v_blinding`.
    /// This is a convenience wrapper around [`RangeProof::prove_multiple`].
    ///
    /// # Example
    /// ```
    /// extern crate rand;
    /// use rand::thread_rng;
    ///
    /// extern crate curve25519_dalek;
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// extern crate merlin;
    /// use merlin::Transcript;
    ///
    /// extern crate bulletproofs;
    /// use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
    ///
    /// # fn main() {
    /// // Generators for Pedersen commitments.  These can be selected
    /// // independently of the Bulletproofs generators.
    /// let pc_gens = PedersenGens::default();
    ///
    /// // Generators for Bulletproofs, valid for proofs up to bitsize 64
    /// // and aggregation size up to 1.
    /// let bp_gens = BulletproofGens::new(64, 1);
    ///
    /// // A secret value we want to prove lies in the range [0, 2^32)
    /// let secret_value = 1037578891u64;
    ///
    /// // The API takes a blinding factor for the commitment.
    /// let blinding = Scalar::random(&mut thread_rng());
    ///
    /// // The proof can be chained to an existing transcript.
    /// // Here we create a transcript with a doctest domain separator.
    /// let mut prover_transcript = Transcript::new(b"doctest example");
    ///
    /// // Create a 32-bit rangeproof.
    /// let (proof, committed_value) = RangeProof::prove_single(
    ///     &bp_gens,
    ///     &pc_gens,
    ///     &mut prover_transcript,
    ///     secret_value,
    ///     &blinding,
    ///     32,
    /// ).expect("A real program could handle errors");
    ///
    /// // Verification requires a transcript with identical initial state:
    /// let mut verifier_transcript = Transcript::new(b"doctest example");
    /// assert!(
    ///     proof
    ///         .verify_single(&bp_gens, &pc_gens, &mut verifier_transcript, &committed_value, 32)
    ///         .is_ok()
    /// );
    /// # }
    /// ```
    pub fn prove_single_with_rng<T: RngCore + CryptoRng>(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        v: u64,
        v_blinding: &Scalar,
        n: usize,
        rng: &mut T,
    ) -> Result<(RangeProof, CompressedRistretto), ProofError> {
        let (p, Vs) = RangeProof::prove_multiple_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            &[v],
            &[*v_blinding],
            n,
            rng,
        )?;
        Ok((p, Vs[0]))
    }

    /// Create a rangeproof for a given pair of value `v` and
    /// blinding scalar `v_blinding`.
    /// This is a convenience wrapper around [`RangeProof::prove_single_with_rng`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn prove_single(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        v: u64,
        v_blinding: &Scalar,
        n: usize,
    ) -> Result<(RangeProof, CompressedRistretto), ProofError> {
        RangeProof::prove_single_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            v,
            v_blinding,
            n,
            &mut thread_rng(),
        )
    }

    /// Create a rangeproof for a set of values.
    ///
    /// # Example
    /// ```
    /// extern crate rand;
    /// use rand::thread_rng;
    ///
    /// extern crate curve25519_dalek;
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// extern crate merlin;
    /// use merlin::Transcript;
    ///
    /// extern crate bulletproofs;
    /// use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
    ///
    /// # fn main() {
    /// // Generators for Pedersen commitments.  These can be selected
    /// // independently of the Bulletproofs generators.
    /// let pc_gens = PedersenGens::default();
    ///
    /// // Generators for Bulletproofs, valid for proofs up to bitsize 64
    /// // and aggregation size up to 16.
    /// let bp_gens = BulletproofGens::new(64, 16);
    ///
    /// // Four secret values we want to prove lie in the range [0, 2^32)
    /// let secrets = [4242344947u64, 3718732727u64, 2255562556u64, 2526146994u64];
    ///
    /// // The API takes blinding factors for the commitments.
    /// let blindings: Vec<_> = (0..4).map(|_| Scalar::random(&mut thread_rng())).collect();
    ///
    /// // The proof can be chained to an existing transcript.
    /// // Here we create a transcript with a doctest domain separator.
    /// let mut prover_transcript = Transcript::new(b"doctest example");
    ///
    /// // Create an aggregated 32-bit rangeproof and corresponding commitments.
    /// let (proof, commitments) = RangeProof::prove_multiple(
    ///     &bp_gens,
    ///     &pc_gens,
    ///     &mut prover_transcript,
    ///     &secrets,
    ///     &blindings,
    ///     32,
    /// ).expect("A real program could handle errors");
    ///
    /// // Verification requires a transcript with identical initial state:
    /// let mut verifier_transcript = Transcript::new(b"doctest example");
    /// assert!(
    ///     proof
    ///         .verify_multiple(&bp_gens, &pc_gens, &mut verifier_transcript, &commitments, 32)
    ///         .is_ok()
    /// );
    /// # }
    /// ```
    pub fn prove_multiple_with_rng<T: RngCore + CryptoRng>(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        values: &[u64],
        blindings: &[Scalar],
        n: usize,
        rng: &mut T,
    ) -> Result<(RangeProof, Vec<CompressedRistretto>), ProofError> {
        use self::dealer::*;
        use self::party::*;

        if values.len() != blindings.len() {
            return Err(ProofError::WrongNumBlindingFactors);
        }

        let dealer = Dealer::new(bp_gens, pc_gens, transcript, n, values.len())?;

        let parties: Vec<_> = values
            .iter()
            .zip(blindings.iter())
            .map(|(&v, &v_blinding)| Party::new(bp_gens, pc_gens, v, v_blinding, n))
            // Collect the iterator of Results into a Result<Vec>, then unwrap it
            .collect::<Result<Vec<_>, _>>()?;

        let (parties, bit_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .enumerate()
            .map(|(j, p)| {
                p.assign_position_with_rng(j, rng)
                    .expect("We already checked the parameters, so this should never happen")
            })
            .unzip();

        let value_commitments: Vec<_> = bit_commitments.iter().map(|c| c.V_j).collect();

        let (dealer, bit_challenge) = dealer.receive_bit_commitments(bit_commitments)?;

        let (parties, poly_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .map(|p| p.apply_challenge_with_rng(&bit_challenge, rng))
            .unzip();

        let (dealer, poly_challenge) = dealer.receive_poly_commitments(poly_commitments)?;

        let proof_shares: Vec<_> = parties
            .into_iter()
            .map(|p| p.apply_challenge(&poly_challenge))
            // Collect the iterator of Results into a Result<Vec>, then unwrap it
            .collect::<Result<Vec<_>, _>>()?;

        let proof = dealer.receive_trusted_shares(&proof_shares)?;

        Ok((proof, value_commitments))
    }

    /// Create a rangeproof for a set of values.
    /// This is a convenience wrapper around [`RangeProof::prove_multiple_with_rng`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn prove_multiple(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        values: &[u64],
        blindings: &[Scalar],
        n: usize,
    ) -> Result<(RangeProof, Vec<CompressedRistretto>), ProofError> {
        RangeProof::prove_multiple_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            values,
            blindings,
            n,
            &mut thread_rng(),
        )
    }

    /// Verifies a rangeproof for a given value commitment \\(V\\).
    ///
    /// This is a convenience wrapper around `verify_multiple` for the `m=1` case.
    pub fn verify_single_with_rng<T: RngCore + CryptoRng>(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        V: &CompressedRistretto,
        n: usize,
        rng: &mut T,
    ) -> Result<(), ProofError> {
        self.verify_multiple_with_rng(bp_gens, pc_gens, transcript, &[*V], n, rng)
    }

    /// Verifies a rangeproof for a given value commitment \\(V\\).
    ///
    /// This is a convenience wrapper around [`RangeProof::verify_single_with_rng`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn verify_single(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        V: &CompressedRistretto,
        n: usize,
    ) -> Result<(), ProofError> {
        self.verify_single_with_rng(bp_gens, pc_gens, transcript, V, n, &mut thread_rng())
    }

    /// Verifies an aggregated rangeproof for the given value commitments.
    pub fn verify_multiple_with_rng<T: RngCore + CryptoRng>(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        value_commitments: &[CompressedRistretto],
        n: usize,
        rng: &mut T,
    ) -> Result<(), ProofError> {
        let m = value_commitments.len();

        // First, replay the "interactive" protocol using the proof
        // data to recompute all challenges.
        if !(n == 8 || n == 16 || n == 32 || n == 64) {
            return Err(ProofError::InvalidBitsize);
        }
        if bp_gens.gens_capacity < n {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        if bp_gens.party_capacity < m {
            return Err(ProofError::InvalidGeneratorsLength);
        }

        transcript.rangeproof_domain_sep(n as u64, m as u64);

        for V in value_commitments.iter() {
            // Allow the commitments to be zero (0 value, 0 blinding)
            // See https://github.com/dalek-cryptography/bulletproofs/pull/248#discussion_r255167177
            transcript.append_point(b"V", V);
        }

        transcript.validate_and_append_point(b"A", &self.A)?;
        transcript.validate_and_append_point(b"S", &self.S)?;

        let y = transcript.challenge_scalar(b"y");
        let z = transcript.challenge_scalar(b"z");
        let zz = z * z;
        let minus_z = -z;

        transcript.validate_and_append_point(b"T_1", &self.T_1)?;
        transcript.validate_and_append_point(b"T_2", &self.T_2)?;

        let x = transcript.challenge_scalar(b"x");

        transcript.append_scalar(b"t_x", &self.t_x);
        transcript.append_scalar(b"t_x_blinding", &self.t_x_blinding);
        transcript.append_scalar(b"e_blinding", &self.e_blinding);

        let w = transcript.challenge_scalar(b"w");

        // Challenge value for batching statements to be verified
        let c = Scalar::random(rng);

        let (x_sq, x_inv_sq, s) = self.ipp_proof.verification_scalars(n * m, transcript)?;
        let s_inv = s.iter().rev();

        let a = self.ipp_proof.a;
        let b = self.ipp_proof.b;

        // Construct concat_z_and_2, an iterator of the values of
        // z^0 * \vec(2)^n || z^1 * \vec(2)^n || ... || z^(m-1) * \vec(2)^n
        let powers_of_2: Vec<Scalar> = util::exp_iter(Scalar::from(2u64)).take(n).collect();
        let concat_z_and_2: Vec<Scalar> = util::exp_iter(z)
            .take(m)
            .flat_map(|exp_z| powers_of_2.iter().map(move |exp_2| exp_2 * exp_z))
            .collect();

        let g = s.iter().map(|s_i| minus_z - a * s_i);
        let h = s_inv
            .zip(util::exp_iter(y.invert()))
            .zip(concat_z_and_2.iter())
            .map(|((s_i_inv, exp_y_inv), z_and_2)| z + exp_y_inv * (zz * z_and_2 - b * s_i_inv));

        let value_commitment_scalars = util::exp_iter(z).take(m).map(|z_exp| c * zz * z_exp);
        let basepoint_scalar = w * (self.t_x - a * b) + c * (delta(n, m, &y, &z) - self.t_x);

        let mega_check = RistrettoPoint::optional_multiscalar_mul(
            iter::once(Scalar::one())
                .chain(iter::once(x))
                .chain(iter::once(c * x))
                .chain(iter::once(c * x * x))
                .chain(x_sq.iter().cloned())
                .chain(x_inv_sq.iter().cloned())
                .chain(iter::once(-self.e_blinding - c * self.t_x_blinding))
                .chain(iter::once(basepoint_scalar))
                .chain(g)
                .chain(h)
                .chain(value_commitment_scalars),
            iter::once(self.A.decompress())
                .chain(iter::once(self.S.decompress()))
                .chain(iter::once(self.T_1.decompress()))
                .chain(iter::once(self.T_2.decompress()))
                .chain(self.ipp_proof.L_vec.iter().map(|L| L.decompress()))
                .chain(self.ipp_proof.R_vec.iter().map(|R| R.decompress()))
                .chain(iter::once(Some(pc_gens.B_blinding)))
                .chain(iter::once(Some(pc_gens.B)))
                .chain(bp_gens.G(n, m).map(|&x| Some(x)))
                .chain(bp_gens.H(n, m).map(|&x| Some(x)))
                .chain(value_commitments.iter().map(|V| V.decompress())),
        )
        .ok_or_else(|| ProofError::VerificationError)?;

        if mega_check.is_identity() {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }

    /// Verifies an aggregated rangeproof for the given value commitments.
    /// This is a convenience wrapper around [`RangeProof::verify_multiple_with_rng`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn verify_multiple(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        value_commitments: &[CompressedRistretto],
        n: usize,
    ) -> Result<(), ProofError> {
        self.verify_multiple_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            value_commitments,
            n,
            &mut thread_rng(),
        )
    }

    /// Serializes the proof into a byte array of \\(2 \lg n + 9\\)
    /// 32-byte elements, where \\(n\\) is the number of secret bits.
    ///
    /// # Layout
    ///
    /// The layout of the range proof encoding is:
    ///
    /// * four compressed Ristretto points \\(A,S,T_1,T_2\\),
    /// * three scalars \\(t_x, \tilde{t}_x, \tilde{e}\\),
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0,R_0\dots,L_{n-1},R_{n-1}\\),
    /// * two scalars \\(a, b\\).
    pub fn to_bytes(&self) -> Vec<u8> {
        // 7 elements: points A, S, T1, T2, scalars tx, tx_bl, e_bl.
        let mut buf = Vec::with_capacity(7 * 32 + self.ipp_proof.serialized_size());
        buf.extend_from_slice(self.A.as_bytes());
        buf.extend_from_slice(self.S.as_bytes());
        buf.extend_from_slice(self.T_1.as_bytes());
        buf.extend_from_slice(self.T_2.as_bytes());
        buf.extend_from_slice(self.t_x.as_bytes());
        buf.extend_from_slice(self.t_x_blinding.as_bytes());
        buf.extend_from_slice(self.e_blinding.as_bytes());
        buf.extend(self.ipp_proof.to_bytes_iter());
        buf
    }

    /// Deserializes the proof from a byte slice.
    ///
    /// Returns an error if the byte slice cannot be parsed into a `RangeProof`.
    pub fn from_bytes(slice: &[u8]) -> Result<RangeProof, ProofError> {
        if slice.len() % 32 != 0 {
            return Err(ProofError::FormatError);
        }
        if slice.len() < 7 * 32 {
            return Err(ProofError::FormatError);
        }

        use crate::util::read32;

        let A = CompressedRistretto(read32(&slice[0 * 32..]));
        let S = CompressedRistretto(read32(&slice[1 * 32..]));
        let T_1 = CompressedRistretto(read32(&slice[2 * 32..]));
        let T_2 = CompressedRistretto(read32(&slice[3 * 32..]));

        let t_x = Scalar::from_canonical_bytes(read32(&slice[4 * 32..]))
            .ok_or(ProofError::FormatError)?;
        let t_x_blinding = Scalar::from_canonical_bytes(read32(&slice[5 * 32..]))
            .ok_or(ProofError::FormatError)?;
        let e_blinding = Scalar::from_canonical_bytes(read32(&slice[6 * 32..]))
            .ok_or(ProofError::FormatError)?;

        let ipp_proof = InnerProductProof::from_bytes(&slice[7 * 32..])?;

        Ok(RangeProof {
            A,
            S,
            T_1,
            T_2,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        })
    }
    /// Transform from Rangeproof to zether proof. Temporary method to start cleaning the
    /// code.
    pub fn to_ZetherProof(
        self,
        ann_y: RistrettoPoint,
        ann_D: RistrettoPoint,
        ann_b: RistrettoPoint,
        ann_y_: RistrettoPoint,
        ann_t: RistrettoPoint,
        res_sk: Scalar,
        res_r: Scalar,
        res_b: Scalar,
    ) -> ZetherProof {
        ZetherProof {
            A: self.A,
            S: self.S,
            T_1: self.T_1,
            T_2: self.T_2,
            t_x: self.t_x,
            t_x_blinding: self.t_x_blinding,
            e_blinding: self.e_blinding,
            ipp_proof: self.ipp_proof,
            ann_y: ann_y.compress(),
            ann_D: ann_D.compress(),
            ann_b: ann_b.compress(),
            ann_y_: ann_y_.compress(),
            ann_t: ann_t.compress(),
            res_sk,
            res_r,
            res_b,
        }
    }
    /// Transform from Rangeproof to zether proof. Temporary method to start cleaning the
    /// code.
    pub fn to_BatchZetherProof(
        self,
        ann_y: RistrettoPoint,
        ann_D: RistrettoPoint,
        ann_b: RistrettoPoint,
        ann_y_: Vec<RistrettoPoint>,
        ann_t: RistrettoPoint,
        res_sk: Scalar,
        res_r: Scalar,
        res_b: Scalar,
    ) -> BatchZetherProof {
        BatchZetherProof {
            nmbr: ann_y_.len(),
            A: self.A,
            S: self.S,
            T_1: self.T_1,
            T_2: self.T_2,
            t_x: self.t_x,
            t_x_blinding: self.t_x_blinding,
            e_blinding: self.e_blinding,
            ipp_proof: self.ipp_proof,
            ann_y: ann_y.compress(),
            ann_D: ann_D.compress(),
            ann_b: ann_b.compress(),
            ann_y_: ann_y_.into_iter().map(|x| x.compress()).collect(),
            ann_t: ann_t.compress(),
            res_sk,
            res_r,
            res_b,
        }
    }
}

impl Serialize for RangeProof {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(&self.to_bytes()[..])
    }
}

impl<'de> Deserialize<'de> for RangeProof {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct RangeProofVisitor;

        impl<'de> Visitor<'de> for RangeProofVisitor {
            type Value = RangeProof;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                formatter.write_str("a valid RangeProof")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<RangeProof, E>
            where
                E: serde::de::Error,
            {
                // Using Error::custom requires T: Display, which our error
                // type only implements when it implements std::error::Error.
                #[cfg(feature = "std")]
                return RangeProof::from_bytes(v).map_err(serde::de::Error::custom);
                // In no-std contexts, drop the error message.
                #[cfg(not(feature = "std"))]
                return RangeProof::from_bytes(v)
                    .map_err(|_| serde::de::Error::custom("deserialization error"));
            }
        }

        deserializer.deserialize_bytes(RangeProofVisitor)
    }
}

#[derive(Clone, Debug)]
/// The zether proof generates a proof of a correct anonymous transaction making use
/// of Bulletproofs.
pub struct ZetherProof {
    /// Commitment to the bits of the value
    A: CompressedRistretto,
    /// Commitment to the blinding factors
    S: CompressedRistretto,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    T_1: CompressedRistretto,
    /// Commitment to the \\(t_2\\) coefficient of \\( t(x) \\)
    T_2: CompressedRistretto,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\(t(x)\\)
    t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the inner-product arguments
    e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    ipp_proof: InnerProductProof,
    /// Sigma protocol messages
    /// Commitment to the blinding factors
    pub ann_y: CompressedRistretto,
    /// Commitment to the blinding factors
    pub ann_D: CompressedRistretto,
    /// Commitment to the blinding factors
    pub ann_b: CompressedRistretto,
    /// Commitment to the blinding factors
    pub ann_y_: CompressedRistretto,
    /// Commitment to the blinding factors
    pub ann_t: CompressedRistretto,
    /// Response to the challenge
    pub res_sk: Scalar,
    /// Response to the challenge
    pub res_r: Scalar,
    /// Response to the challenge
    pub res_b: Scalar,
}

impl ZetherProof {
    /// Generate for multiple in the zether scenario. Because of using ElGamal
    /// encryptions in Zether, we need to twist a bit the proof an verification
    /// given that the ElGamal bases does not satisfy the requirements of a
    /// Pedersen commitment base.
    /// The main difference with the bulletproof, except of the sigma protocol,
    /// is how we apply the challenge to the committed polynomial.
    /// In this scenario, we omit the first coefficient of the polynomial.
    pub fn prove_multiple(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        values: &[u64],
        blindings: &[Scalar],
        n: usize,

        pk_sender: &RistrettoPoint,
        pk_receiver: &RistrettoPoint,
        enc_balance_after_transfer: &(RistrettoPoint, RistrettoPoint),
        enc_amount_sender: &(RistrettoPoint, RistrettoPoint),
        sk_sender: &Scalar,
        comm_rnd: &Scalar,
    ) -> Result<(ZetherProof, Vec<CompressedRistretto>), ProofError> {
        use self::dealer::*;
        use self::party::*;

        if values.len() != blindings.len() {
            return Err(ProofError::WrongNumBlindingFactors);
        }

        if values.len() != 2 {
            return Err(ProofError::WrongNumZetherProof);
        }

        let dealer = Dealer::new(bp_gens, pc_gens, transcript, n, values.len())?;

        let parties: Vec<_> = values
            .iter()
            .zip(blindings.iter())
            .map(|(&v, &v_blinding)| Party::new(bp_gens, pc_gens, v, v_blinding, n))
            // Collect the iterator of Results into a Result<Vec>, then unwrap it
            .collect::<Result<Vec<_>, _>>()?;

        let (parties, bit_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .enumerate()
            .map(|(j, p)| {
                p.assign_position(j)
                    .expect("We already checked the parameters, so this should never happen")
            })
            .unzip();

        let value_commitments: Vec<_> = bit_commitments.iter().map(|c| c.V_j).collect();

        let (dealer, bit_challenge) = dealer.receive_bit_commitments(bit_commitments)?;

        let (parties, poly_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .map(|p| p.apply_challenge(&bit_challenge))
            .unzip();

        let (dealer, poly_challenge) = dealer.receive_poly_commitments(poly_commitments)?;

        let proof_shares: Vec<_> = parties
            .into_iter()
            .map(|p| p.apply_challenge_zether(&poly_challenge))
            // Collect the iterator of Results into a Result<Vec>, then unwrap it
            .collect::<Result<Vec<_>, _>>()?;

        let proof = dealer.receive_shares_and_generate_zether(
            &Scalar::from(values[0]),
            &Scalar::from(values[1]),
            &proof_shares,
            pk_sender,
            pk_receiver,
            enc_balance_after_transfer,
            enc_amount_sender,
            sk_sender,
            comm_rnd,
        )?;

        Ok((proof, value_commitments))
    }

    /// Verifies an aggregated rangeproof for the given value commitments together
    /// with the sigma protocol. Note that in the 'mega check' we omit the
    /// verification involving the pedersen commitments of the values within a range
    /// to include the ElGamal encryptions instead. A simple translation would
    /// not suffice, given that ElGamal encryptions cannot be seen as Pedersen
    /// commitments.
    pub fn verify_multiple(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        value_commitments: &[CompressedRistretto],
        n: usize,

        pk_sender: &RistrettoPoint,
        pk_receiver: &RistrettoPoint,
        enc_balance_after_transfer: &(RistrettoPoint, RistrettoPoint),
        enc_amount_sender: &(RistrettoPoint, RistrettoPoint),
        enc_amount_receiver: &(RistrettoPoint, RistrettoPoint),
    ) -> Result<(Scalar, Scalar, Scalar), ProofError> {
        let m = value_commitments.len();

        // First, replay the "interactive" protocol using the proof
        // data to recompute all challenges.
        if !(n == 8 || n == 16 || n == 32 || n == 64) {
            return Err(ProofError::InvalidBitsize);
        }
        if bp_gens.gens_capacity < n {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        if bp_gens.party_capacity < m {
            return Err(ProofError::InvalidGeneratorsLength);
        }

        transcript.rangeproof_domain_sep(n as u64, m as u64);

        for V in value_commitments.iter() {
            // Allow the commitments to be zero (0 value, 0 blinding)
            // See https://github.com/dalek-cryptography/bulletproofs/pull/248#discussion_r255167177
            transcript.append_point(b"V", V);
        }

        transcript.validate_and_append_point(b"A", &self.A)?;
        transcript.validate_and_append_point(b"S", &self.S)?;

        let y = transcript.challenge_scalar(b"y");
        let z = transcript.challenge_scalar(b"z");
        let zz = z * z;
        let zzz = zz * z;
        let minus_z = -z;

        transcript.validate_and_append_point(b"T_1", &self.T_1)?;
        transcript.validate_and_append_point(b"T_2", &self.T_2)?;

        let x = transcript.challenge_scalar(b"x");

        transcript.append_scalar(b"t_x", &self.t_x);
        transcript.append_scalar(b"t_x_blinding", &self.t_x_blinding);
        transcript.append_scalar(b"e_blinding", &self.e_blinding);

        let w = transcript.challenge_scalar(b"w");

        let (x_sq, x_inv_sq, s) = self.ipp_proof.verification_scalars(n * m, transcript)?;
        let s_inv = s.iter().rev();

        let a = self.ipp_proof.a;
        let b = self.ipp_proof.b;

        // Construct concat_z_and_2, an iterator of the values of
        // z^0 * \vec(2)^n || z^1 * \vec(2)^n || ... || z^(m-1) * \vec(2)^n
        let powers_of_2: Vec<Scalar> = util::exp_iter(Scalar::from(2u64)).take(n).collect();
        let concat_z_and_2: Vec<Scalar> = util::exp_iter(z)
            .take(m)
            .flat_map(|exp_z| powers_of_2.iter().map(move |exp_2| exp_2 * exp_z))
            .collect();

        let g = s.iter().map(|s_i| minus_z - a * s_i);
        let h = s_inv
            .zip(util::exp_iter(y.invert()))
            .zip(concat_z_and_2.iter())
            .map(|((s_i_inv, exp_y_inv), z_and_2)| z + exp_y_inv * (zz * z_and_2 - b * s_i_inv));

        let basepoint_scalar = w * (self.t_x - a * b); // + c * (delta(n, m, &y, &z) - self.t_x);

        let challenge_sigma = transcript.challenge_scalar(b"challenge_sigma");

        // We break the mega check in three, otherwise it because too big to compile in --release mode

        let mega_check1 = RistrettoPoint::optional_multiscalar_mul(
            iter::once(Scalar::one())
                .chain(iter::once(Scalar::one()))
                .chain(iter::once(Scalar::one()))
                .chain(iter::once(-self.res_sk))
                .chain(iter::once(-self.res_r))
                .chain(iter::once(-self.res_r))
                .chain(iter::once(challenge_sigma))
                .chain(iter::once(challenge_sigma))
                .chain(iter::once(challenge_sigma)),
            iter::once(self.ann_y.decompress())
                .chain(iter::once(self.ann_D.decompress()))
                .chain(iter::once(self.ann_y_.decompress()))
                .chain(iter::once(Some(pc_gens.B)))
                .chain(iter::once(Some(pc_gens.B)))
                .chain(iter::once(Some(pk_sender - pk_receiver)))
                .chain(iter::once(Some(*pk_sender)))
                .chain(iter::once(Some(enc_amount_sender.1)))
                .chain(iter::once(Some(
                    enc_amount_sender.0 - enc_amount_receiver.0,
                ))),
        )
        .ok_or_else(|| ProofError::VerificationError)?;

        let mega_check2 = RistrettoPoint::optional_multiscalar_mul(
            iter::once(Scalar::one())
                .chain(iter::once(Scalar::one()))
                .chain(iter::once(-self.res_b))
                .chain(iter::repeat(zz).take(2))
                .chain(iter::repeat(zzz).take(2))
                .chain(iter::once(challenge_sigma))
                .chain(iter::once(challenge_sigma)),
            iter::once(self.ann_b.decompress())
                .chain(iter::once(self.ann_t.decompress()))
                .chain(iter::once(Some(pc_gens.B)))
                .chain(
                    iter::repeat(Some(
                        challenge_sigma * enc_amount_sender.0 - self.res_sk * enc_amount_sender.1,
                    ))
                    .take(2),
                )
                .chain(
                    iter::repeat(Some(
                        challenge_sigma * enc_balance_after_transfer.0
                            - self.res_sk * enc_balance_after_transfer.1,
                    ))
                    .take(2),
                )
                .chain(iter::once(Some(
                    -(self.t_x - delta(n, 2, &y, &z)) * pc_gens.B
                        - self.t_x_blinding * pc_gens.B_blinding,
                )))
                .chain(iter::once(Some(
                    x * self.T_1.decompress().unwrap() + (x * x) * self.T_2.decompress().unwrap(),
                ))),
        )
        .ok_or_else(|| ProofError::VerificationError)?;

        let mega_check3 = RistrettoPoint::optional_multiscalar_mul(
            iter::once(Scalar::one())
                .chain(iter::once(x))
                .chain(x_sq.iter().cloned())
                .chain(x_inv_sq.iter().cloned())
                .chain(iter::once(-self.e_blinding))
                .chain(iter::once(basepoint_scalar))
                .chain(g)
                .chain(h),
            iter::once(self.A.decompress())
                .chain(iter::once(self.S.decompress()))
                .chain(self.ipp_proof.L_vec.iter().map(|L| L.decompress()))
                .chain(self.ipp_proof.R_vec.iter().map(|R| R.decompress()))
                .chain(iter::once(Some(pc_gens.B_blinding)))
                .chain(iter::once(Some(pc_gens.B)))
                .chain(bp_gens.G(n, m).map(|&x| Some(x)))
                .chain(bp_gens.H(n, m).map(|&x| Some(x))),
        )
        .ok_or_else(|| ProofError::VerificationError)?;

        if mega_check1.is_identity() && mega_check2.is_identity() && mega_check3.is_identity() {
            Ok((x, y, z))
        } else {
            Err(ProofError::VerificationError)
        }
    }

    /// Serializes the proof into a byte array of \\(2 \lg n + 9\\)
    /// 32-byte elements, where \\(n\\) is the number of secret bits.
    ///
    /// # Layout
    ///
    /// The layout of the range proof encoding is:
    ///
    /// * 9 compressed Ristretto points \\(A,S,T_1,T_2\\),
    /// * 6 scalars \\(t_x, \tilde{t}_x, \tilde{e}\\),
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0,R_0\dots,L_{n-1},R_{n-1}\\),
    /// * two scalars \\(a, b\\).

    pub fn to_bytes(&self) -> Vec<u8> {
        // 15 elements: points A, S, T1, T2, ann_y, ann_D, ann_b, ann_y_, ann_t, scalars tx, tx_bl, e_bl, res_sk, res_r, res_b.
        let mut buf = Vec::with_capacity(15 * 32 + self.ipp_proof.serialized_size());
        buf.extend_from_slice(self.A.as_bytes());
        buf.extend_from_slice(self.S.as_bytes());
        buf.extend_from_slice(self.T_1.as_bytes());
        buf.extend_from_slice(self.T_2.as_bytes());
        buf.extend_from_slice(self.t_x.as_bytes());
        buf.extend_from_slice(self.t_x_blinding.as_bytes());
        buf.extend_from_slice(self.e_blinding.as_bytes());
        buf.extend_from_slice(self.ann_y.as_bytes());
        buf.extend_from_slice(self.ann_D.as_bytes());
        buf.extend_from_slice(self.ann_b.as_bytes());
        buf.extend_from_slice(self.ann_y_.as_bytes());
        buf.extend_from_slice(self.ann_t.as_bytes());
        buf.extend_from_slice(self.res_sk.as_bytes());
        buf.extend_from_slice(self.res_r.as_bytes());
        buf.extend_from_slice(self.res_b.as_bytes());
        // XXX this costs an extra alloc
        buf.extend_from_slice(self.ipp_proof.to_bytes().as_slice());
        buf
    }

    /// Deserializes the proof from a byte slice.
    ///
    /// Returns an error if the byte slice cannot be parsed into a `RangeProof`.
    pub fn from_bytes(slice: &[u8]) -> Result<ZetherProof, ProofError> {
        if slice.len() % 32 != 0 {
            return Err(ProofError::FormatError);
        }
        if slice.len() < 15 * 32 {
            return Err(ProofError::FormatError);
        }

        use util::read32;

        let A = CompressedRistretto(read32(&slice[0 * 32..]));
        let S = CompressedRistretto(read32(&slice[1 * 32..]));
        let T_1 = CompressedRistretto(read32(&slice[2 * 32..]));
        let T_2 = CompressedRistretto(read32(&slice[3 * 32..]));

        let t_x = Scalar::from_canonical_bytes(read32(&slice[4 * 32..]))
            .ok_or(ProofError::FormatError)?;
        let t_x_blinding = Scalar::from_canonical_bytes(read32(&slice[5 * 32..]))
            .ok_or(ProofError::FormatError)?;
        let e_blinding = Scalar::from_canonical_bytes(read32(&slice[6 * 32..]))
            .ok_or(ProofError::FormatError)?;

        let ann_y = CompressedRistretto(read32(&slice[7 * 32..]));
        let ann_D = CompressedRistretto(read32(&slice[8 * 32..]));
        let ann_b = CompressedRistretto(read32(&slice[9 * 32..]));
        let ann_y_ = CompressedRistretto(read32(&slice[10 * 32..]));
        let ann_t = CompressedRistretto(read32(&slice[11 * 32..]));

        let res_sk = Scalar::from_canonical_bytes(read32(&slice[12 * 32..]))
            .ok_or(ProofError::FormatError)?;
        let res_r = Scalar::from_canonical_bytes(read32(&slice[13 * 32..]))
            .ok_or(ProofError::FormatError)?;
        let res_b = Scalar::from_canonical_bytes(read32(&slice[14 * 32..]))
            .ok_or(ProofError::FormatError)?;

        let ipp_proof = InnerProductProof::from_bytes(&slice[15 * 32..])?;

        Ok(ZetherProof {
            A,
            S,
            T_1,
            T_2,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
            ann_y,
            ann_D,
            ann_b,
            ann_y_,
            ann_t,
            res_sk,
            res_r,
            res_b,
        })
    }
}

impl Serialize for ZetherProof {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(&self.to_bytes()[..])
    }
}

impl<'de> Deserialize<'de> for ZetherProof {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ZetherProofVisitor;

        impl<'de> Visitor<'de> for ZetherProofVisitor {
            type Value = ZetherProof;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                formatter.write_str("a valid ZetherProof")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<ZetherProof, E>
            where
                E: serde::de::Error,
            {
                ZetherProof::from_bytes(v).map_err(serde::de::Error::custom)
            }
        }

        deserializer.deserialize_bytes(ZetherProofVisitor)
    }
}

/// Compute
/// \\[
/// \delta(y,z) = (z - z^{2}) \langle \mathbf{1}, {\mathbf{y}}^{n \cdot m} \rangle - \sum_{j=0}^{m-1} z^{j+3} \cdot \langle \mathbf{1}, {\mathbf{2}}^{n \cdot m} \rangle
/// \\]
fn delta(n: usize, m: usize, y: &Scalar, z: &Scalar) -> Scalar {
    let sum_y = util::sum_of_powers(y, n * m);
    let sum_2 = util::sum_of_powers(&Scalar::from(2u64), n);
    let sum_z = util::sum_of_powers(z, m);

    (z - z * z) * sum_y - z * z * z * sum_2 * sum_z
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::generators::PedersenGens;

    #[test]
    fn test_delta() {
        let mut rng = rand::thread_rng();
        let y = Scalar::random(&mut rng);
        let z = Scalar::random(&mut rng);

        // Choose n = 256 to ensure we overflow the group order during
        // the computation, to check that that's done correctly
        let n = 256;

        // code copied from previous implementation
        let z2 = z * z;
        let z3 = z2 * z;
        let mut power_g = Scalar::zero();
        let mut exp_y = Scalar::one(); // start at y^0 = 1
        let mut exp_2 = Scalar::one(); // start at 2^0 = 1
        for _ in 0..n {
            power_g += (z - z2) * exp_y - z3 * exp_2;

            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }

        assert_eq!(power_g, delta(n, 1, &y, &z),);
    }

    /// Given a bitsize `n`, test the following:
    ///
    /// 1. Generate `m` random values and create a proof they are all in range;
    /// 2. Serialize to wire format;
    /// 3. Deserialize from wire format;
    /// 4. Verify the proof.
    fn singleparty_create_and_verify_helper(n: usize, m: usize) {
        // Split the test into two scopes, so that it's explicit what
        // data is shared between the prover and the verifier.

        // Use bincode for serialization
        //use bincode; // already present in lib.rs

        // Both prover and verifier have access to the generators and the proof
        let max_bitsize = 64;
        let max_parties = 8;
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(max_bitsize, max_parties);

        // Prover's scope
        let (proof_bytes, value_commitments) = {
            use self::rand::Rng;
            let mut rng = rand::thread_rng();

            // 0. Create witness data
            let (min, max) = (0u64, ((1u128 << n) - 1) as u64);
            let values: Vec<u64> = (0..m).map(|_| rng.gen_range(min, max)).collect();
            let blindings: Vec<Scalar> = (0..m).map(|_| Scalar::random(&mut rng)).collect();

            // 1. Create the proof
            let mut transcript = Transcript::new(b"AggregatedRangeProofTest");
            let (proof, value_commitments) = RangeProof::prove_multiple(
                &bp_gens,
                &pc_gens,
                &mut transcript,
                &values,
                &blindings,
                n,
            )
            .unwrap();

            // 2. Return serialized proof and value commitments
            (bincode::serialize(&proof).unwrap(), value_commitments)
        };

        // Verifier's scope
        {
            // 3. Deserialize
            let proof: RangeProof = bincode::deserialize(&proof_bytes).unwrap();

            // 4. Verify with the same customization label as above
            let mut transcript = Transcript::new(b"AggregatedRangeProofTest");

            assert!(proof
                .verify_multiple(&bp_gens, &pc_gens, &mut transcript, &value_commitments, n)
                .is_ok());
        }
    }

    #[test]
    fn create_and_verify_n_32_m_1() {
        singleparty_create_and_verify_helper(32, 1);
    }

    #[test]
    fn create_and_verify_n_32_m_2() {
        singleparty_create_and_verify_helper(32, 2);
    }

    #[test]
    fn create_and_verify_n_32_m_4() {
        singleparty_create_and_verify_helper(32, 4);
    }

    #[test]
    fn create_and_verify_n_32_m_8() {
        singleparty_create_and_verify_helper(32, 8);
    }

    #[test]
    fn create_and_verify_n_64_m_1() {
        singleparty_create_and_verify_helper(64, 1);
    }

    #[test]
    fn create_and_verify_n_64_m_2() {
        singleparty_create_and_verify_helper(64, 2);
    }

    #[test]
    fn create_and_verify_n_64_m_4() {
        singleparty_create_and_verify_helper(64, 4);
    }

    #[test]
    fn create_and_verify_n_64_m_8() {
        singleparty_create_and_verify_helper(64, 8);
    }

    #[test]
    fn detect_dishonest_party_during_aggregation() {
        use self::dealer::*;
        use self::party::*;

        use crate::errors::MPCError;

        // Simulate four parties, two of which will be dishonest and use a 64-bit value.
        let m = 4;
        let n = 32;

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(n, m);

        use self::rand::Rng;
        let mut rng = rand::thread_rng();
        let mut transcript = Transcript::new(b"AggregatedRangeProofTest");

        // Parties 0, 2 are honest and use a 32-bit value
        let v0 = rng.gen::<u32>() as u64;
        let v0_blinding = Scalar::random(&mut rng);
        let party0 = Party::new(&bp_gens, &pc_gens, v0, v0_blinding, n).unwrap();

        let v2 = rng.gen::<u32>() as u64;
        let v2_blinding = Scalar::random(&mut rng);
        let party2 = Party::new(&bp_gens, &pc_gens, v2, v2_blinding, n).unwrap();

        // Parties 1, 3 are dishonest and use a 64-bit value
        let v1 = rng.gen::<u64>();
        let v1_blinding = Scalar::random(&mut rng);
        let party1 = Party::new(&bp_gens, &pc_gens, v1, v1_blinding, n).unwrap();

        let v3 = rng.gen::<u64>();
        let v3_blinding = Scalar::random(&mut rng);
        let party3 = Party::new(&bp_gens, &pc_gens, v3, v3_blinding, n).unwrap();

        let dealer = Dealer::new(&bp_gens, &pc_gens, &mut transcript, n, m).unwrap();

        let (party0, bit_com0) = party0.assign_position(0).unwrap();
        let (party1, bit_com1) = party1.assign_position(1).unwrap();
        let (party2, bit_com2) = party2.assign_position(2).unwrap();
        let (party3, bit_com3) = party3.assign_position(3).unwrap();

        let (dealer, bit_challenge) = dealer
            .receive_bit_commitments(vec![bit_com0, bit_com1, bit_com2, bit_com3])
            .unwrap();

        let (party0, poly_com0) = party0.apply_challenge(&bit_challenge);
        let (party1, poly_com1) = party1.apply_challenge(&bit_challenge);
        let (party2, poly_com2) = party2.apply_challenge(&bit_challenge);
        let (party3, poly_com3) = party3.apply_challenge(&bit_challenge);

        let (dealer, poly_challenge) = dealer
            .receive_poly_commitments(vec![poly_com0, poly_com1, poly_com2, poly_com3])
            .unwrap();

        let share0 = party0.apply_challenge(&poly_challenge).unwrap();
        let share1 = party1.apply_challenge(&poly_challenge).unwrap();
        let share2 = party2.apply_challenge(&poly_challenge).unwrap();
        let share3 = party3.apply_challenge(&poly_challenge).unwrap();

        match dealer.receive_shares(&[share0, share1, share2, share3]) {
            Err(MPCError::MalformedProofShares { bad_shares }) => {
                assert_eq!(bad_shares, vec![1, 3]);
            }
            Err(_) => {
                panic!("Got wrong error type from malformed shares");
            }
            Ok(_) => {
                panic!("The proof was malformed, but it was not detected");
            }
        }
    }

    #[test]
    fn detect_dishonest_dealer_during_aggregation() {
        use self::dealer::*;
        use self::party::*;
        use crate::errors::MPCError;

        // Simulate one party
        let m = 1;
        let n = 32;

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(n, m);

        use self::rand::Rng;
        let mut rng = rand::thread_rng();
        let mut transcript = Transcript::new(b"AggregatedRangeProofTest");

        let v0 = rng.gen::<u32>() as u64;
        let v0_blinding = Scalar::random(&mut rng);
        let party0 = Party::new(&bp_gens, &pc_gens, v0, v0_blinding, n).unwrap();

        let dealer = Dealer::new(&bp_gens, &pc_gens, &mut transcript, n, m).unwrap();

        // Now do the protocol flow as normal....

        let (party0, bit_com0) = party0.assign_position(0).unwrap();

        let (dealer, bit_challenge) = dealer.receive_bit_commitments(vec![bit_com0]).unwrap();

        let (party0, poly_com0) = party0.apply_challenge(&bit_challenge);

        let (_dealer, mut poly_challenge) =
            dealer.receive_poly_commitments(vec![poly_com0]).unwrap();

        // But now simulate a malicious dealer choosing x = 0
        poly_challenge.x = Scalar::zero();

        let maybe_share0 = party0.apply_challenge(&poly_challenge);

        assert!(maybe_share0.unwrap_err() == MPCError::MaliciousDealer);
    }

    use rand::thread_rng;

    #[test]
    fn create_and_verify_zether_proof() {
        let b_sent = 1234u64;
        let b_remaining = 123u64;
        let b_initial = &b_sent + &b_remaining;

        // Bulletproof part
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(64, 2);

        let blinding_1 = Scalar::random(&mut thread_rng());
        let blinding_2 = Scalar::random(&mut thread_rng());

        let mut prover_transcript = Transcript::new(b"doctest example");

        let commitment_1 = pc_gens.commit(Scalar::from(b_sent), blinding_1);
        let commitment_2 = pc_gens.commit(Scalar::from(b_remaining), blinding_2);

        let sk = Scalar::random(&mut thread_rng());
        let g = pc_gens.B;

        let y = &sk * &g; // public key sender
        let y_ = RistrettoPoint::random(&mut thread_rng()); // public key receiver

        let random_encryption = Scalar::random(&mut thread_rng());
        let (Cl, Cr) = (
            &Scalar::from(b_initial) * &g + &random_encryption * &y,
            &random_encryption * &g,
        );

        let blinding_factor = Scalar::random(&mut thread_rng());
        let (C, D) = (
            &Scalar::from(b_sent) * &g + &blinding_factor * &y,
            &blinding_factor * &g,
        );
        let (C_, D_) = (
            &Scalar::from(b_sent) * &g + &blinding_factor * &y_,
            &blinding_factor * &g,
        );

        let Cln = Cl - C; // encrypted balance after sending
        let Crn = Cr - D; // "

        let (zether_proof, committed_value) = ZetherProof::prove_multiple(
            &bp_gens,
            &pc_gens,
            &mut prover_transcript,
            &[b_sent, b_remaining],
            &[blinding_1, blinding_2],
            64,
            &y,
            &y_,
            &(Cln, Crn),
            &(C, D),
            &sk,
            &blinding_factor,
        )
        .expect("A real program could handle errors");

        let commitments: Vec<RistrettoPoint> = committed_value
            .iter()
            .map(|p| {
                p.decompress()
                    .expect("commitments in zether proof should be able to be decompressed")
            })
            .collect();

        let original_commitments = vec![commitment_1, commitment_2];
        assert!(
            committed_value.len() == 2
                && commitment_1.compress() == committed_value[0]
                && commitment_2.compress() == committed_value[1]
        );
        println!(
            "{:?}, {:?}, {:?}",
            commitment_1.compress(),
            commitment_2.compress(),
            committed_value
        );

        // Just making sure that the byte conversion works
        let bytes = zether_proof.to_bytes();
        let from_bytes = ZetherProof::from_bytes(&bytes).unwrap();
        let mut verifier_transcript = Transcript::new(b"doctest example");

        assert!(from_bytes
            .verify_multiple(
                &bp_gens,
                &pc_gens,
                &mut verifier_transcript,
                &[commitment_1.compress(), commitment_2.compress()],
                64,
                &y,
                &y_,
                &(Cln, Crn),
                &(C, D),
                &(C_, D_),
            )
            .is_ok());
    }
    #[test]
    fn create_and_verify_invalid_zether_proof() {
        let b_sent = 1234u64;
        let b_remaining = 123u64;
        let b_initial = &b_sent + &b_remaining;

        // Bulletproof part
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(64, 2);

        let blinding_1 = Scalar::random(&mut thread_rng());
        let blinding_2 = Scalar::random(&mut thread_rng());

        let mut prover_transcript = Transcript::new(b"doctest example");

        let commitment_1 = pc_gens.commit(Scalar::from(b_sent), blinding_1);
        // We commit a different value to the one used to generate the proof
        let commitment_2 = pc_gens.commit(-Scalar::from(b_remaining), blinding_2);

        let sk = Scalar::random(&mut thread_rng());
        let g = pc_gens.B;

        let y = &sk * &g; // public key sender
        let y_ = RistrettoPoint::random(&mut thread_rng()); // public key receiver

        let random_encryption = Scalar::random(&mut thread_rng());
        let (Cl, Cr) = (
            &Scalar::from(b_initial) * &g + &random_encryption * &y,
            &random_encryption * &g,
        );

        let blinding_factor = Scalar::random(&mut thread_rng());
        let (C, D) = (
            &Scalar::from(b_sent) * &g + &blinding_factor * &y,
            &blinding_factor * &g,
        );
        let (C_, D_) = (
            &Scalar::from(b_sent) * &g + &blinding_factor * &y_,
            &blinding_factor * &g,
        );

        let Cln = Cl - C; // encrypted balance after sending
        let Crn = Cr - D; // "

        let (zether_proof, _committed_value) = ZetherProof::prove_multiple(
            &bp_gens,
            &pc_gens,
            &mut prover_transcript,
            &[b_sent, b_remaining],
            &[blinding_1, blinding_2],
            64,
            &y,
            &y_,
            &(Cln, Crn),
            &(C, D),
            &sk,
            &blinding_factor,
        )
        .expect("A real program could handle errors");

        let mut verifier_transcript = Transcript::new(b"doctest example");

        assert!(zether_proof
            .verify_multiple(
                &bp_gens,
                &pc_gens,
                &mut verifier_transcript,
                &[commitment_1.compress(), commitment_2.compress()],
                64,
                &y,
                &y_,
                &(Cln, Crn),
                &(C, D),
                &(C_, D_),
            )
            .is_err());
    }
}
