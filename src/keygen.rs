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

pub struct SigmaProof {
    pub ri: decaf377::Element,
    pub ui: decaf377::Fr,
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
    pub commitment: Vec<decaf377::Element>,
    pub sigma: SigmaProof,
}

pub fn generate_keyshare(t: u8, n: u8, i: u8) -> RoundOne {
    // TODO: check t, n
    let rng = &mut thread_rng();

    // sample t random values ai0..ai(t-1) as coefficients
    let mut coeffs = Vec::new();
    for _ in 0..t - 1 {
        coeffs.push(decaf377::Fr::rand(rng));
    }

    let aio = coeffs[0].clone();
    let aio_commitment = aio * decaf377::basepoint();

    // compute a proof of knowledge to ai0
    let sigma = SigmaProof::new(aio_commitment, aio, "TODO: ANTI-REPLAY CONTEXT", i.into());

    let public_commitments = coeffs
        .iter()
        .map(|coeff| coeff * decaf377::basepoint())
        .collect::<Vec<_>>();

    RoundOne {
        commitment: public_commitments,
        sigma,
    }
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

        let mut shares = Vec::new();
        for i in 0..n {
            shares.push(generate_keyshare(t, n, i));
        }

        verify_keyshares(shares, "TODO: ANTI-REPLAY CONTEXT").unwrap();
    }
}
