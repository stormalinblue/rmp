use super::biguint::BigUInt;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::ops::{Add, Neg, Sub};

#[derive(Clone)]
pub enum BigInt {
    Negative(BigUInt),
    Zero,
    Positive(BigUInt),
}

impl From<BigUInt> for BigInt {
    fn from(uint: BigUInt) -> BigInt {
        BigInt::Positive(uint)
    }
}

impl Add<&BigInt> for &BigInt {
    type Output = BigInt;

    fn add(self: Self, other: &BigInt) -> BigInt {
        match (self, other) {
            (BigInt::Zero, BigInt::Zero) => BigInt::Zero,
            (BigInt::Zero, _) => other.clone(),
            (_, BigInt::Zero) => self.clone(),
            (BigInt::Positive(left), BigInt::Positive(right)) => BigInt::Positive(left + right),
            (BigInt::Negative(left), BigInt::Negative(right)) => BigInt::Negative(left + right),
            (BigInt::Positive(left), BigInt::Negative(right)) => match left.cmp(right) {
                Ordering::Equal => BigInt::Zero,
                Ordering::Greater => BigInt::Positive((left - right).unwrap()),
                Ordering::Less => BigInt::Negative((right - left).unwrap()),
            },
            (BigInt::Negative(left), BigInt::Positive(right)) => match left.cmp(right) {
                Ordering::Equal => BigInt::Zero,
                Ordering::Greater => BigInt::Negative((left - right).unwrap()),
                Ordering::Less => BigInt::Positive((right - left).unwrap()),
            },
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
            (BigInt::Positive(left), BigInt::Positive(right)) => match left.cmp(right) {
                Ordering::Equal => BigInt::Zero,
                Ordering::Greater => BigInt::Positive((left - right).unwrap()),
                Ordering::Less => BigInt::Negative((right - left).unwrap()),
            },
            (BigInt::Negative(left), BigInt::Negative(right)) => match left.cmp(right) {
                Ordering::Equal => BigInt::Zero,
                Ordering::Greater => BigInt::Negative((left - right).unwrap()),
                Ordering::Less => BigInt::Positive((right - left).unwrap()),
            },
            (BigInt::Positive(left), BigInt::Negative(right)) => BigInt::Positive(left + right),
            (BigInt::Negative(left), BigInt::Positive(right)) => BigInt::Negative(left + right),
        }
    }
}

impl Neg for BigInt {
    type Output = BigInt;
    fn neg(self) -> Self::Output {
        match self {
            BigInt::Zero => BigInt::Zero,
            BigInt::Negative(abs) => BigInt::Positive(abs),
            BigInt::Positive(abs) => BigInt::Negative(abs),
        }
    }
}

impl Debug for BigInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BigInt::Zero => write!(f, "0"),
            BigInt::Negative(absolute) => {
                write!(f, "-{:?}", absolute)
            }
            BigInt::Positive(absolute) => {
                write!(f, "+{:?}", absolute)
            }
        }
    }
}
