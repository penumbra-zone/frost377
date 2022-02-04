use ark_ff::Field;
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
use ark_ff::{One, PrimeField, UniformRand};
use rand::thread_rng;

#[derive(Debug, Clone)]
pub struct RoundOne {
    /// decaf377-encoded point that represents the participant's commitment
    commitment: Vec<decaf377::Element>,

    // proof of knowledge to ai0
    ri: decaf377::Element,
    ui: decaf377::Fr,
}

impl RoundOne {
    fn for_participant(participant: &Participant) -> Self {
        RoundOne {
            commitment: participant.commitments.clone(),
            ri: participant.ri,
            ui: participant.ui,
        }
    }
}

pub fn verify_keyshares(
    participants: Vec<RoundOne>,
    context_string: &str,
) -> Result<(), anyhow::Error> {
    for (i, participant) in participants.iter().enumerate() {
        let index = i as u32;
        // verify RoundOne.ri = g^ui * theta_0^-cl
        let ci = blake2b_simd::Params::default()
            .personal(b"keygen_challenge")
            .to_state()
            .update(&index.to_le_bytes())
            .update(context_string.as_bytes())
            .update(participant.commitment[0].compress().0.as_ref())
            .update(participant.ri.compress().0.as_ref())
            .finalize();

        let ci = participant.commitment[0] * -decaf377::Fr::from_le_bytes_mod_order(ci.as_bytes());

        // verify ui*G + Ci0*-ci = Ri
        if participant.ri != (decaf377::basepoint() * participant.ui) + ci {
            return Err(anyhow::anyhow!("could not verify participant's key share"));
        }
    }

    Ok(())
}

#[derive(Debug, Clone)]
pub struct DKGKey {
    verification_share: decaf377::Element,
    private_share: decaf377::Fr,
    group_public_key: decaf377::Element,
}

pub struct Participant {
    secret_coeffs: Vec<decaf377::Fr>,
    commitments: Vec<decaf377::Element>,
    ri: decaf377::Element,
    ui: decaf377::Fr,
    index: u32,
}

// evaluates the polynomial using Horner's method
// (https://en.wikipedia.org/wiki/Horner%27s_method) at x
fn evaluate_polynomial(x: decaf377::Fr, coeffs: Vec<decaf377::Fr>) -> decaf377::Fr {
    let mut result = decaf377::Fr::zero();

    for (i, coeff) in coeffs.iter().rev().enumerate() {
        result += coeff;

        if i != coeffs.len() - 1 {
            result *= x;
        }
    }
    result
}

impl Participant {
    pub fn new(index: u32, t: u32) -> Self {
        let rng = &mut thread_rng();

        let secret_coeffs = (0..t - 1)
            .map(|_| decaf377::Fr::rand(rng))
            .collect::<Vec<_>>();

        let aio = secret_coeffs[0].clone();
        let aio_commitment = aio * decaf377::basepoint();

        // compute a proof of knowledge for ai0
        let k = decaf377::Fr::rand(&mut thread_rng());
        let ri = k * decaf377::basepoint();
        let ci = blake2b_simd::Params::default()
            .personal(b"keygen_challenge")
            .to_state()
            .update(&index.to_le_bytes())
            .update("TODO: ANTI-REPLAY CONTEXT".as_bytes())
            .update(aio_commitment.compress().0.as_ref())
            .update(ri.compress().0.as_ref())
            .finalize();
        let ui = k + aio * decaf377::Fr::from_le_bytes_mod_order(ci.as_bytes());

        let public_commitments = secret_coeffs
            .iter()
            .map(|coeff| coeff * decaf377::basepoint())
            .collect::<Vec<_>>();

        Participant {
            secret_coeffs,
            commitments: public_commitments,
            index,
            ri: ri,
            ui: ui,
        }
    }
    fn share_for_counterparty(&self, counterparty_index: u32) -> RoundTwo {
        let fi = evaluate_polynomial(
            decaf377::Fr::from(counterparty_index),
            self.secret_coeffs.clone(),
        );

        RoundTwo {
            participant_index: counterparty_index,
            counterparty_index: self.index,
            fi,
        }
    }
}

#[derive(Debug, Clone)]
pub struct RoundTwo {
    pub participant_index: u32,
    pub counterparty_index: u32,
    pub fi: decaf377::Fr,
}

impl RoundTwo {
    fn verify(
        &self,
        counterparty_commitments: Vec<decaf377::Element>,
        secret_coeffs: Vec<decaf377::Fr>,
        ai0_commitments: Vec<decaf377::Element>,
        t: u32,
        n: u32,
    ) -> Result<DKGKey, anyhow::Error> {
        // step 2: verify the counterparty's shares, abort if the check fails
        // compute fl(i)*G
        let gfli = self.fi * decaf377::basepoint();
        println!("fi: {:?}", self.fi);

        let mut res = decaf377::Element::default();
        for k in 0..t - 1 {
            let mut ikmodq = decaf377::Fr::from(
                self.participant_index.pow(k as u32) as u64 % decaf377::Fr::characteristic()[0],
            );
            res = res + (counterparty_commitments[k as usize] * ikmodq);
        }

        println!("{:?}", res);
        println!("{:?}", gfli);
        if res != gfli {
            Err(anyhow::anyhow!("verification failed"))?
        }

        // compute the long-lived private signing share
        let mut private_share = decaf377::Fr::zero();
        for i in 1..n {
            let i32 = i as u32;
            private_share =
                private_share + evaluate_polynomial(decaf377::Fr::from(i32), secret_coeffs.clone());
        }

        // compute the public verification key and the group's public key
        let verification_share = decaf377::basepoint() * private_share;

        let mut group_public_key = decaf377::Element::default();
        for i in 1..n {
            group_public_key = group_public_key + ai0_commitments[i as usize]
        }

        Ok(DKGKey {
            verification_share,
            private_share,
            group_public_key,
        })
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_roundone_generate_verify() {
        let t = 3;
        let n = 5;

        let mut participants = Vec::new();
        for i in 0..n {
            participants.push(Participant::new(i, t));
        }

        let mut round1_messages = Vec::new();
        for participant in participants.iter() {
            round1_messages.push(RoundOne::for_participant(participant));
        }
        verify_keyshares(round1_messages, "TODO: ANTI-REPLAY CONTEXT").unwrap();
    }
    #[test]
    fn test_full_dkg() {
        let t = 3;
        let n = 5;

        let mut participants = Vec::new();
        for i in 0..n {
            participants.push(Participant::new(i, t));
        }

        let mut round1_messages = Vec::new();
        for participant in participants.iter() {
            round1_messages.push(RoundOne::for_participant(participant));
        }
        verify_keyshares(round1_messages.clone(), "TODO: ANTI-REPLAY CONTEXT").unwrap();

        let mut aio_commitments = Vec::new();
        for participant in participants.iter() {
            aio_commitments.push(*participant.commitments.clone().first().unwrap());
        }

        // each Pi sends to each other participant Pl (l, fi(l))
        let mut group_public_keys = Vec::new();
        for (i, participant) in participants.iter().enumerate() {
            for l in 0..n {
                if i == l as usize {
                    continue;
                }
                // (l, fi(l))
                // send participant l participant i's (l, fi(l))
                let pi_message = participant.share_for_counterparty(l);
                println!("{:?}", pi_message);

                // participant i verifies their shares for participant l
                let dkg_key = pi_message
                    .clone()
                    .verify(
                        participant.commitments.clone(),
                        participants[l as usize].secret_coeffs.clone(),
                        aio_commitments.clone(),
                        t,
                        n
                    )
                    .unwrap();

                group_public_keys.push(dkg_key.group_public_key);
                println!("VERIFICATION SUCCESS");
                println!("{:?}", dkg_key);
            }
        }

        // verify that every participant produced the same group public key
        for pubkey in group_public_keys.iter() {
            println!("{:?}", pubkey);
        }
        group_public_keys
            .iter()
            .fold(group_public_keys[0].clone(), |acc, x| {
                assert_eq!(acc, *x);
                acc
            });
    }
}
