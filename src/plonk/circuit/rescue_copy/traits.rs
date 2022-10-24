use plonk::circuit::Engine;

#[derive(Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum HashFamily {
    Rescue,
    Poseidon,
    RescuePrime,
}

#[derive(Copy, Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum CustomGate {
    QuinticWidth4,
    QuinticWidth3,
    None,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Step {
    Double {
        index: usize,
    },
    Add {
        left: usize,
        right: usize,
    },
}

#[derive(Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Sbox {
    Alpha(u64),
    AlphaInverse(Vec<u64>, u64),
    AddChain(Vec<Step>, u64),
}

impl From<addchain::Step> for Step {
    fn from(value: addchain::Step) -> Self {
        match value {
            addchain::Step::Add { left, right } => Step::Add { left, right },
            addchain::Step::Double { index } => Step::Double { index },
        }
    }
}

impl std::fmt::Debug for Sbox {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Alpha(alpha) => write!(f, "sbox x^{}", alpha),
            Self::AlphaInverse(vec, alpha) => write!(f, "inverse sbox [u64; {}] for x^{}", vec.len(), alpha),
            Self::AddChain(_, alpha) => write!(f, "add chain inverse sbox for x^{}", alpha),
        }
    }
}

pub trait HashParams<E: Engine, const RATE: usize, const WIDTH: usize>:
    Clone + Send + Sync + serde::Serialize + serde::de::DeserializeOwned
{
    #[inline]
    fn allows_specialization(&self) -> bool {
        false
    }
    fn hash_family(&self) -> HashFamily;
    fn constants_of_round(&self, round: usize) -> &[E::Fr; WIDTH];
    fn mds_matrix(&self) -> &[[E::Fr; WIDTH]; WIDTH];
    fn number_of_full_rounds(&self) -> usize;
    fn number_of_partial_rounds(&self) -> usize;
    fn alpha(&self) -> &Sbox;
    fn alpha_inv(&self) -> &Sbox;
    fn optimized_round_constants(&self) -> &[[E::Fr; WIDTH]];
    fn optimized_mds_matrixes(&self) -> (&[[E::Fr; WIDTH]; WIDTH], &[[[E::Fr; WIDTH]; WIDTH]]);
    fn custom_gate(&self) -> CustomGate;
    fn use_custom_gate(&mut self, gate: CustomGate);
    fn specialized_affine_transformation_for_round(&self, state: &mut [E::Fr; WIDTH], round_constants: &[E::Fr; WIDTH]) {
        unimplemented!("not implemented by default");
    }
}
