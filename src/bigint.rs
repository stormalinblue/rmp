use super::biguint::BigUInt;
use std::cmp::{Ord, Ordering};
use std::fmt::Debug;
use std::ops::{Add, Neg, Sub};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Sign {
    Positive,
    Negative,
}

impl Sign {
    fn flipped(&self) -> Sign {
        match self {
            Sign::Positive => Self::Negative,
            Sign::Negative => Self::Positive,
        }
    }

    fn flip(&mut self) {
        *self = self.flipped()
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Nonzero {
    sign: Sign,
    mantissa: BigUInt,
}

impl PartialOrd for &Nonzero {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for &Nonzero {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.sign, other.sign) {
            (Sign::Positive, Sign::Negative) => Ordering::Greater,
            (Sign::Negative, Sign::Positive) => Ordering::Less,
            (Sign::Positive, Sign::Positive) => self.mantissa.cmp(&other.mantissa),
            (Sign::Negative, Sign::Negative) => other.mantissa.cmp(&self.mantissa),
        }
    }
}

#[derive(Clone)]
pub enum BigInt {
    Zero,
    Nonzero(Nonzero),
}

impl BigInt {
    fn nonzero_unchecked(sign: Sign, mantissa: BigUInt) -> Self {
        BigInt::Nonzero(Nonzero { sign, mantissa })
    }

    fn positive_unchecked(mantissa: BigUInt) -> Self {
        BigInt::Nonzero(Nonzero {
            sign: Sign::Positive,
            mantissa,
        })
    }

    fn negative_unchecked(mantissa: BigUInt) -> Self {
        BigInt::Nonzero(Nonzero {
            sign: Sign::Negative,
            mantissa,
        })
    }
}

impl From<BigUInt> for BigInt {
    fn from(uint: BigUInt) -> BigInt {
        if uint.is_zero() {
            BigInt::Zero
        } else {
            BigInt::nonzero_unchecked(Sign::Positive, uint)
        }
    }
}

impl Add<&BigInt> for &BigInt {
    type Output = BigInt;

    fn add(self: Self, other: &BigInt) -> BigInt {
        match (self, other) {
            (BigInt::Zero, BigInt::Zero) => BigInt::Zero,
            (BigInt::Zero, _) => other.clone(),
            (_, BigInt::Zero) => self.clone(),
            (
                BigInt::Nonzero(Nonzero {
                    sign: sign_a,
                    mantissa: man_a,
                }),
                BigInt::Nonzero(Nonzero {
                    sign: sign_b,
                    mantissa: man_b,
                }),
            ) => {
                if sign_a == sign_b {
                    return BigInt::nonzero_unchecked(*sign_a, man_a + man_b);
                } else {
                    match man_a.cmp(man_b) {
                        Ordering::Equal => BigInt::Zero,
                        Ordering::Greater => {
                            BigInt::positive_unchecked(unsafe { man_a.sub_unchecked(man_b) })
                        }
                        Ordering::Less => {
                            BigInt::negative_unchecked(unsafe { man_b.sub_unchecked(man_a) })
                        }
                    }
                }
            }
        }
    }
}

impl Sub<&BigInt> for &BigInt {
    type Output = BigInt;

    fn sub(self: Self, other: &BigInt) -> BigInt {
        match (self, other) {
            (BigInt::Zero, BigInt::Zero) => BigInt::Zero,
            (BigInt::Zero, _) => other.clone(),
            (_, BigInt::Zero) => self.clone(),
            (
                BigInt::Nonzero(Nonzero {
                    sign: sign_a,
                    mantissa: man_a,
                }),
                BigInt::Nonzero(Nonzero {
                    sign: sign_b,
                    mantissa: man_b,
                }),
            ) => {
                if sign_a == sign_b {
                    return BigInt::nonzero_unchecked(*sign_a, man_a + man_b);
                } else {
                    match man_a.cmp(man_b) {
                        Ordering::Equal => BigInt::Zero,
                        Ordering::Greater => {
                            BigInt::negative_unchecked(unsafe { man_a.sub_unchecked(man_b) })
                        }
                        Ordering::Less => {
                            BigInt::positive_unchecked(unsafe { man_b.sub_unchecked(man_a) })
                        }
                    }
                }
            }
        }
    }
}

impl Neg for BigInt {
    type Output = BigInt;
    fn neg(self) -> Self::Output {
        match self {
            BigInt::Zero => BigInt::Zero,
            BigInt::Nonzero(Nonzero { sign, mantissa }) => {
                BigInt::nonzero_unchecked(sign.flipped(), mantissa)
            }
        }
    }
}

impl Debug for BigInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BigInt::Zero => write!(f, "0"),
            BigInt::Nonzero(Nonzero { sign, mantissa }) => match sign {
                Sign::Positive => {
                    write!(f, "-{:?}", mantissa)
                }
                Sign::Negative => {
                    write!(f, "+{:?}", mantissa)
                }
            },
        }
    }
}
