use std::collections::BTreeMap;

/// keygen: implements the keygen step of FROST
///
/// see: https://eprint.iacr.org/2020/852.pdf (page 12)
// TODO:
// - more documentation
// - rework API design, think about api misuse potential
// - add secure delete/zeroize-on-drop
use ark_ff::{Field, PrimeField, UniformRand, Zero};
use rand::thread_rng;

#[derive(Debug, Clone)]
pub struct RoundOne {
    /// commitments to <ai0, ai1, ai2 ...
    commitments: Vec<decaf377::Element>,
    index: u32,

    // proof of knowledge to ai0
    ri: decaf377::Element,
    ui: decaf377::Fr,
}

#[derive(Debug, Clone)]
pub struct DKGKey {
    verification_share: decaf377::Element,
    private_share: decaf377::Fr,
    group_public_key: decaf377::Element,
}

#[derive(Debug, Clone)]
pub struct Share {
    pub x: u32,
    pub y: decaf377::Fr,
}

pub struct DKGOutput {
    pub group_public_key: decaf377::Element,
    pub private_share: decaf377::Fr,
    pub participant_index: u32,
}

#[derive(Clone)]
pub struct Participant {
    ri: decaf377::Element,
    ui: decaf377::Fr,
    secret_coeffs: Vec<decaf377::Fr>,
    pub commitments: Vec<decaf377::Element>,
    pub index: u32,

    my_share: Share,
    other_shares: Vec<Share>,
    counterparty_commitments: BTreeMap<u32, Vec<decaf377::Element>>,
}

// evaluates the polynomial specified by `coeffs` using Horner's method
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

        let secret_coeffs = (0..t).map(|_| decaf377::Fr::rand(rng)).collect::<Vec<_>>();

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
            commitments: public_commitments,
            my_share: Share {
                x: index,
                y: evaluate_polynomial(decaf377::Fr::from(index), secret_coeffs.clone()),
            },
            secret_coeffs,
            index,
            ri: ri,
            ui: ui,
            other_shares: Vec::new(),
            counterparty_commitments: BTreeMap::new(),
        }
    }
    pub fn round_one(&self) -> RoundOne {
        RoundOne {
            commitments: self.commitments.clone(),
            ri: self.ri,
            ui: self.ui,
            index: self.index,
        }
    }
    pub fn verify_roundone(&mut self, others: Vec<RoundOne>) -> Result<(), anyhow::Error> {
        let context_string = "TODO: ANTI-REPLAY CONTEXT";
        for (i, participant) in others.iter().enumerate() {
            if participant.index == self.index {
                continue;
            }
            // verify RoundOne.ri = g^ui * theta_0^-cl
            let ci = blake2b_simd::Params::default()
                .personal(b"keygen_challenge")
                .to_state()
                .update(&participant.index.to_le_bytes())
                .update(context_string.as_bytes())
                .update(participant.commitments[0].compress().0.as_ref())
                .update(participant.ri.compress().0.as_ref())
                .finalize();

            let ci =
                participant.commitments[0] * -decaf377::Fr::from_le_bytes_mod_order(ci.as_bytes());

            // verify ui*G + Ci0*-ci = Ri
            if participant.ri != (decaf377::basepoint() * participant.ui) + ci {
                return Err(anyhow::anyhow!("could not verify participant's key share"));
            }

            // store this participant's commitments
            self.counterparty_commitments
                .insert(participant.index, participant.commitments.clone());
        }
        Ok(())
    }

    pub fn round_two(&self, counterparty_index: u32) -> RoundTwo {
        let fi = evaluate_polynomial(
            decaf377::Fr::from(counterparty_index),
            self.secret_coeffs.clone(),
        );

        RoundTwo {
            for_participant: counterparty_index,
            from_participant: self.index,
            share: Share {
                x: counterparty_index,
                y: fi,
            },
        }
    }

    pub fn verify_and_add_roundtwo_response(
        &mut self,
        counterparty_response: &RoundTwo,
    ) -> Result<(), anyhow::Error> {
        let commitments = self
            .counterparty_commitments
            .get(&counterparty_response.from_participant)
            .ok_or(anyhow::anyhow!("counterparty commitments not found"))?;

        // verify that the round two response is correct
        counterparty_response.verify(commitments.clone())?;
        println!("verified round two response");

        self.other_shares.push(counterparty_response.share.clone());

        Ok(())
    }

    pub fn finalize(&self) -> Result<DKGOutput, anyhow::Error> {
        println!("shares: {:?}", self.other_shares);
        // compute the group's public key
        let mut group_public_key = self.commitments[0];
        for (i, commitment) in self.counterparty_commitments.iter() {
            group_public_key = group_public_key + commitment[0];
        }

        // compute the private share
        let mut private_share = self.my_share.y;
        for other_share in self.other_shares.iter() {
            private_share = private_share + other_share.y;
        }

        Ok(DKGOutput {
            group_public_key,
            private_share,
            participant_index: self.index,
        })
    }
}

#[derive(Debug, Clone)]
pub struct RoundTwo {
    pub for_participant: u32,
    pub from_participant: u32,
    pub share: Share,
}

impl RoundTwo {
    pub fn verify(
        &self,
        counterparty_commitments: Vec<decaf377::Element>,
    ) -> Result<(), anyhow::Error> {
        // step 2: verify the counterparty's shares, abort if the check fails
        // compute fl(i)*G
        let gfli = self.share.y * decaf377::basepoint();

        // verify fl(i)*G = sum(Cl(k) * i^k)
        let mut result = decaf377::Element::default();
        for (i, commitment) in counterparty_commitments.iter().rev().enumerate() {
            result += commitment;

            if i != counterparty_commitments.len() - 1 {
                result = result * decaf377::Fr::from(self.for_participant);
            }
        }
        if result != gfli {
            Err(anyhow::anyhow!("verification failed"))?
        }

        Ok(())
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
            round1_messages.push(participant.round_one());
        }
        for mut participant in participants {
            participant
                .verify_roundone(round1_messages.clone())
                .unwrap();
        }
    }
    #[test]
    fn test_full_dkg() {
        let t = 3;
        let n = 5;

        let mut participants = Vec::new();
        for i in 1..n + 1 {
            participants.push(Participant::new(i, t));
        }

        let mut round1_messages = Vec::new();
        for participant in participants.iter() {
            round1_messages.push(participant.round_one());
        }
        for participant in participants.iter_mut() {
            participant
                .verify_roundone(round1_messages.clone())
                .unwrap();
        }

        let other_participants = participants.clone();

        // each Pi sends to each other participant Pl (l, fi(l))
        for (i, participant) in participants.iter_mut().enumerate() {
            for (l, participant_other) in other_participants.iter().enumerate() {
                if participant.index == participant_other.index {
                    continue;
                }
                let round2_message = participant_other.round_two(participant.index);

                println!("verifying round two message: {:?}", round2_message);

                participant
                    .verify_and_add_roundtwo_response(&round2_message)
                    .unwrap();
            }
        }

        let dkg_pubkey = participants[0].finalize().unwrap().group_public_key;
        for participant in participants.iter() {
            if participant.finalize().unwrap().group_public_key != dkg_pubkey {
                panic!("group public key mismatch");
            }
        }
    }
}
