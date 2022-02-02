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

pub struct RoundTwo {
    pub index: u16,
    pub fi: decaf377::Fr,
}

impl RoundTwo {
    fn new(secret_coeffs: Vec<decaf377::Fr>, i: u16) -> Self {
        // evaluates the polynomial using Horner's method
        // (https://en.wikipedia.org/wiki/Horner%27s_method) at x
        let poly = |x: decaf377::Fr| {
            let mut result = secret_coeffs[0].clone();
            for i in 1..secret_coeffs.len() {
                result = result * x + secret_coeffs[i];
            }
            result
        };

        // evaluate polynomial
        let fi = poly(decaf377::Fr::from(i));

        RoundTwo { index: i, fi }
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
