/// keygen: implements the keygen step of FROST
/// 

pub struct SigmaProof {
    pub ri: decaf377::Fr, 
    pub uj: decaf377::Fq,
}
pub struct RoundOne {
    /// decaf377-encoded point that represents the participant's commitment
    pub commitment: decaf377::Fr,
    pub sigma: SigmaProof
}
