use ark_ff::Zero;
/// keygen: implements the keygen step of FROST
///
/// see: https://eprint.iacr.org/2020/852.pdf (page 12)
// TODO:
// - more documentation
// - implement round 2
// - rework API design, think about api misuse potential
// - add secure delete/zeroize-on-drop
//
use ark_ff::{PrimeField, UniformRand};
use rand::thread_rng;

#[derive(Debug, Clone)]
struct SigmaProof {
    ri: decaf377::Element,
    ui: decaf377::Fr,
}

impl SigmaProof {
    pub fn new(
        aio_commitment: decaf377::Element,
        aio: decaf377::Fr,
        context_string: &str,
        i: usize,
    ) -> Self {
        let k = decaf377::Fr::rand(&mut thread_rng());
        let ri = k * decaf377::basepoint();

        let ci = blake2b_simd::Params::default()
            .personal(b"keygen_challenge")
            .to_state()
            .update(&i.to_le_bytes())
            .update(context_string.as_bytes())
            .update(aio_commitment.compress().0.as_ref())
            .update(ri.compress().0.as_ref())
            .finalize();

        let cie = decaf377::Fr::from_le_bytes_mod_order(ci.as_bytes());
        let ui = k + aio * cie;

        SigmaProof { ri, ui }
    }
}

#[derive(Debug, Clone)]
pub struct RoundOne {
    /// decaf377-encoded point that represents the participant's commitment
    commitment: Vec<decaf377::Element>,
    sigma: SigmaProof,
}

impl RoundOne {
    fn new(secret_coeffs: Vec<decaf377::Fr>, t: u16, n: u16, i: u16) -> Self {
        let aio = secret_coeffs[0].clone();
        let aio_commitment = aio * decaf377::basepoint();

        // compute a proof of knowledge to ai0
        let sigma = SigmaProof::new(aio_commitment, aio, "TODO: ANTI-REPLAY CONTEXT", i.into());

        let public_commitments = secret_coeffs
            .iter()
            .map(|coeff| coeff * decaf377::basepoint())
            .collect::<Vec<_>>();

        RoundOne {
            commitment: public_commitments,
            sigma,
        }
    }
}

pub struct DKGKey {
    verification_share: decaf377::Element,
    private_share: decaf377::Fr,
    group_public_key: decaf377::Element,
}

#[derive(Debug, Clone)]
pub struct RoundTwo {
    pub index: u16,
    pub fi: decaf377::Fr,
}
// evaluates the polynomial using Horner's method
// (https://en.wikipedia.org/wiki/Horner%27s_method) at x
fn evaluate_polynomial(x: decaf377::Fr, coeffs: Vec<decaf377::Fr>) -> decaf377::Fr {
    let mut result = coeffs[0].clone();
    for i in 1..coeffs.len() {
        result = result * x + coeffs[i];
    }
    result
}

impl RoundTwo {
    fn new(secret_coeffs: Vec<decaf377::Fr>, i: u16) -> Self {
        let fi = evaluate_polynomial(decaf377::Fr::from(i), secret_coeffs);

        RoundTwo { index: i, fi }
    }
    fn verify(
        &self,
        counterparty_shares: Vec<RoundTwo>,
        secret_coeffs: Vec<decaf377::Fr>,
        commitments: Vec<decaf377::Element>,
    ) -> Result<DKGKey, anyhow::Error> {
        // step 2: verify the counterparty's shares, abort if the check fails
        for share in counterparty_shares.iter() {
            let gfli = decaf377::basepoint()
                * evaluate_polynomial(decaf377::Fr::from(share.index), secret_coeffs.clone());

            let mut res = decaf377::Element::default();
            for (k, commitment) in commitments.iter().enumerate() {
                let ikmodq = decaf377::Fr::from(share.index.pow(k.try_into().unwrap()));

                res = res + commitment * ikmodq;
            }
            if res != gfli {
                Err(anyhow::anyhow!("verification failed"))?
            }
        }

        // compute the long-lived private signing share
        let mut private_share = decaf377::Fr::zero();
        for i in 0..secret_coeffs.len() {
            let i32 = i as u32;
            private_share =
                private_share + evaluate_polynomial(decaf377::Fr::from(i32), secret_coeffs.clone());
        }

        // compute the public verification key and the group's public key
        let verification_share = decaf377::basepoint() * private_share;

        let mut group_public_key = decaf377::Element::default();
        for i in 0..secret_coeffs.len() {
            group_public_key = group_public_key + commitments[i];
        }

        Ok(DKGKey {
            verification_share,
            private_share,
            group_public_key,
        })
    }
}

pub fn generate_keyshare(t: u8, n: u8, i: u8) -> Vec<decaf377::Fr> {
    // TODO: check t, n
    let rng = &mut thread_rng();

    // sample t random values ai0..ai(t-1) as coefficients
    let mut coeffs = Vec::new();
    for _ in 0..t - 1 {
        coeffs.push(decaf377::Fr::rand(rng));
    }

    coeffs
}

pub fn verify_keyshares(
    participants: Vec<RoundOne>,
    context_string: &str,
) -> Result<(), anyhow::Error> {
    for (i, participant) in participants.iter().enumerate() {
        // verify RoundOne.ri = g^ui * theta_0^-cl
        let ci = blake2b_simd::Params::default()
            .personal(b"keygen_challenge")
            .to_state()
            .update(&i.to_le_bytes())
            .update(context_string.as_bytes())
            .update(participant.commitment[0].compress().0.as_ref())
            .update(participant.sigma.ri.compress().0.as_ref())
            .finalize();

        let ci = participant.commitment[0] * -decaf377::Fr::from_le_bytes_mod_order(ci.as_bytes());

        if participant.sigma.ri != ci + (decaf377::basepoint() * participant.sigma.ui) {
            return Err(anyhow::anyhow!("could not verify participant's key share"));
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_full_dkg() {
        let t = 3;
        let n = 5;

        let mut round1_messages = Vec::new();
        let mut shares = Vec::new();
        for i in 0..n {
            let share = generate_keyshare(t, n, i);
            let round1 = RoundOne::new(share.clone(), t.into(), n.into(), i.into());
            round1_messages.push(round1);
            shares.push(share)
        }

        verify_keyshares(round1_messages.clone(), "TODO: ANTI-REPLAY CONTEXT").unwrap();

        let mut round2_messages = Vec::new();
        let mut result_keys = Vec::new();
        for i in 0..n {
            let round2 = RoundTwo::new(shares[i as usize].clone(), i.into());
            round2_messages.push(round2);
        }
        for (i, round2) in round2_messages.iter().enumerate() {
            let shares = shares[i].clone();
            let dkg_key = round2
                .verify(
                    round2_messages.clone(),
                    shares,
                    round1_messages[i].commitment.clone(),
                )
                .unwrap();
            result_keys.push(dkg_key);
        }
    }
    #[test]
    fn test_roundone_generate_verify() {
        let t = 3;
        let n = 5;

        let mut round1_messages = Vec::new();
        for i in 0..n {
            let share = generate_keyshare(t, n, i);
            let round1 = RoundOne::new(share, t.into(), n.into(), i.into());
            round1_messages.push(round1);
        }

        verify_keyshares(round1_messages, "TODO: ANTI-REPLAY CONTEXT").unwrap();
    }
}
