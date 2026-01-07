use super::biguint::BigUInt;
use std::fmt::Debug;
use std::ops::Add;

#[derive(Clone)]
enum BigInt {
    Negative(BigUInt),
    Zero,
    Positive(BigUInt),
}
/*
 * Maintain invariant:
 *
 * Top bit is always 0
 *
 */

impl Add<&BigInt> for &BigInt {
    type Output = BigInt;

    fn add(self: Self, b: &BigInt) -> BigInt {
        todo!();
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
                write!(f, "{:?}", absolute)
            }
        }
    }
}
