use super::biguint::BigUInt;
use std::cmp::{Ord, Ordering};
use std::fmt;
use std::ops::{Add, AddAssign, Mul, Neg, Sub, SubAssign};

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

impl PartialOrd for Nonzero {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Nonzero {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.sign, other.sign) {
            (Sign::Positive, Sign::Negative) => Ordering::Greater,
            (Sign::Negative, Sign::Positive) => Ordering::Less,
            (Sign::Positive, Sign::Positive) => self.mantissa.cmp(&other.mantissa),
            (Sign::Negative, Sign::Negative) => other.mantissa.cmp(&self.mantissa),
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
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

    fn is_nonnegative(&self) -> bool {
        match self {
            BigInt::Zero => true,
            BigInt::Nonzero(Nonzero {
                sign: Sign::Positive,
                ..
            }) => true,
            _ => false,
        }
    }
}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BigInt {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (BigInt::Zero, BigInt::Zero) => Ordering::Equal,
            (BigInt::Nonzero(Nonzero { sign, .. }), BigInt::Zero) => match sign {
                Sign::Positive => Ordering::Greater,
                Sign::Negative => Ordering::Less,
            },
            (BigInt::Zero, BigInt::Nonzero(Nonzero { sign, .. })) => match sign {
                Sign::Positive => Ordering::Less,
                Sign::Negative => Ordering::Greater,
            },
            (BigInt::Nonzero(a), BigInt::Nonzero(b)) => a.cmp(b),
        }
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

impl From<u64> for BigInt {
    fn from(uint: u64) -> BigInt {
        if uint == 0 {
            BigInt::Zero
        } else {
            BigInt::nonzero_unchecked(Sign::Positive, BigUInt::from(uint))
        }
    }
}

impl From<i32> for BigInt {
    fn from(int: i32) -> BigInt {
        match int.cmp(&0) {
            Ordering::Equal => BigInt::Zero,
            Ordering::Greater => BigInt::positive_unchecked(BigUInt::from(int as u64)),
            Ordering::Less => BigInt::negative_unchecked(BigUInt::from((-int) as u64)),
        }
    }
}

impl From<i64> for BigInt {
    fn from(int: i64) -> BigInt {
        match int.cmp(&0) {
            Ordering::Equal => BigInt::Zero,
            Ordering::Greater => BigInt::positive_unchecked(BigUInt::from(int as u64)),
            Ordering::Less => BigInt::negative_unchecked(BigUInt::from((-int) as u64)),
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
                        Ordering::Greater => BigInt::nonzero_unchecked(*sign_a, unsafe {
                            man_a.sub_unchecked(man_b)
                        }),
                        Ordering::Less => BigInt::nonzero_unchecked(*sign_b, unsafe {
                            man_b.sub_unchecked(man_a)
                        }),
                    }
                }
            }
        }
    }
}

impl AddAssign<&BigInt> for BigInt {
    fn add_assign(&mut self, other: &BigInt) {
        match self {
            BigInt::Zero => *self = other.clone(),
            BigInt::Nonzero(a) => match other {
                BigInt::Zero => {}
                BigInt::Nonzero(b) => {
                    if a.sign == b.sign {
                        a.mantissa += &b.mantissa;
                    } else {
                        match a.mantissa.cmp(&b.mantissa) {
                            Ordering::Equal => *self = BigInt::Zero,
                            Ordering::Greater => unsafe {
                                a.mantissa.sub_assign_unchecked(&b.mantissa);
                            },
                            Ordering::Less => {
                                // Optimization: Some sort of rev_mul_assign_unchecked in BigUInt
                                a.mantissa = unsafe { b.mantissa.sub_unchecked(&a.mantissa) }
                            }
                        }
                    }
                }
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
                    match man_a.cmp(man_b) {
                        Ordering::Equal => BigInt::Zero,
                        Ordering::Greater => BigInt::nonzero_unchecked(*sign_a, unsafe {
                            man_a.sub_unchecked(man_b)
                        }),
                        Ordering::Less => BigInt::nonzero_unchecked(sign_a.flipped(), unsafe {
                            man_b.sub_unchecked(man_a)
                        }),
                    }
                } else {
                    return BigInt::nonzero_unchecked(*sign_a, man_a + man_b);
                }
            }
        }
    }
}

impl SubAssign<&BigInt> for BigInt {
    fn sub_assign(&mut self, other: &BigInt) {
        match self {
            BigInt::Zero => *self = other.clone(),
            BigInt::Nonzero(a) => match other {
                BigInt::Zero => {}
                BigInt::Nonzero(b) => {
                    if a.sign != b.sign {
                        a.mantissa += &b.mantissa;
                    } else {
                        match a.mantissa.cmp(&b.mantissa) {
                            Ordering::Equal => *self = BigInt::Zero,
                            Ordering::Greater => unsafe {
                                a.mantissa.sub_assign_unchecked(&b.mantissa);
                            },
                            Ordering::Less => {
                                a.sign.flip();
                                a.mantissa = unsafe { b.mantissa.sub_unchecked(&a.mantissa) }
                            }
                        }
                    }
                }
            },
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

impl Mul<u32> for &BigInt {
    type Output = BigInt;

    fn mul(self, rhs: u32) -> Self::Output {
        if rhs == 0 {
            BigInt::Zero
        } else {
            match self {
                BigInt::Zero => BigInt::Zero,
                BigInt::Nonzero(a) => BigInt::nonzero_unchecked(a.sign, &a.mantissa * rhs),
            }
        }
    }
}

impl Mul<&BigInt> for &BigInt {
    type Output = BigInt;

    fn mul(self, rhs: &BigInt) -> Self::Output {
        match (self, rhs) {
            (BigInt::Zero, _) => BigInt::Zero,
            (_, BigInt::Zero) => BigInt::Zero,
            (BigInt::Nonzero(a), BigInt::Nonzero(b)) => {
                if a.sign == b.sign {
                    BigInt::positive_unchecked(&a.mantissa * &b.mantissa)
                } else {
                    BigInt::negative_unchecked(&a.mantissa * &b.mantissa)
                }
            }
        }
    }
}

impl fmt::LowerHex for BigInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BigInt::Zero => f.pad_integral(true, "", "0"),
            BigInt::Nonzero(Nonzero { sign, mantissa }) => match sign {
                Sign::Positive => f.pad_integral(true, "", &format!("{:x}", &mantissa)),
                Sign::Negative => f.pad_integral(false, "", &format!("{:x}", &mantissa)),
            },
        }
    }
}

impl fmt::Display for BigInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BigInt::Zero => f.pad_integral(true, "", "0"),
            BigInt::Nonzero(Nonzero { sign, mantissa }) => match sign {
                Sign::Positive => f.pad_integral(true, "", &format!("{}", &mantissa)),
                Sign::Negative => f.pad_integral(false, "", &format!("{}", &mantissa)),
            },
        }
    }
}

impl fmt::Debug for BigInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        return write!(f, "{}", self);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_i32_compares_correctly_to_zero() {
        let minus_10 = BigInt::from(-10i32);
        let plus_10 = BigInt::from(10i32);
        let zero = BigInt::from(0i32);

        assert_eq!(zero, BigInt::Zero);
        assert!(&minus_10 < &BigInt::Zero);
        assert!(&plus_10 > &BigInt::Zero);
    }

    #[test]
    fn from_i64_compares_correctly_to_zero() {
        let minus_10 = BigInt::from(-10i64);
        let plus_10 = BigInt::from(10i64);
        let zero = BigInt::from(0i64);

        assert_eq!(zero, BigInt::Zero);
        assert!(&minus_10 < &BigInt::Zero);
        assert!(&plus_10 > &BigInt::Zero);
    }

    #[test]
    fn add_eq_corresponds_to_add_fib() -> () {
        let mut a_add = BigInt::from(1u64);
        let mut b_add = BigInt::from(1u64);

        let mut a_add_eq = BigInt::from(1u64);
        let mut b_add_eq = BigInt::from(1u64);

        for _ in 0..3000 {
            let next_a_add = b_add.clone();
            b_add = b_add.add(&a_add);
            a_add = next_a_add;

            let next_a_add_eq = b_add_eq.clone();
            b_add_eq.add_assign(&a_add_eq);
            a_add_eq = next_a_add_eq;

            assert_eq!(a_add, a_add_eq, "a not equal");
            assert_eq!(b_add, b_add_eq, "b not equal");
        }
    }

    #[test]
    fn sub_reverses_fib_step() -> () {
        let mut a_add_eq = BigInt::from(1u64);
        let mut b_add_eq = BigInt::from(1u64);

        for _ in 0..3000 {
            let prev_a = a_add_eq.clone();
            let prev_b = b_add_eq.clone();
            b_add_eq.add_assign(&a_add_eq);
            assert_eq!(prev_a, (&b_add_eq - &prev_b), "a not equal");
            a_add_eq = prev_b;
        }
    }

    #[test]
    fn sub_reverses_neg_fib_step() -> () {
        let mut a_add_eq = BigInt::from(-1);
        let mut b_add_eq = BigInt::from(-1);

        for _ in 0..3000 {
            let prev_a = a_add_eq.clone();
            let prev_b = b_add_eq.clone();
            b_add_eq.add_assign(&a_add_eq);
            assert_eq!(prev_a, (&b_add_eq - &prev_b), "a not equal");
            a_add_eq = prev_b;
        }
    }

    #[test]
    fn sub_assign_reverses_fib_step() -> () {
        let mut a_add_eq = BigInt::from(1u64);
        let mut b_add_eq = BigInt::from(1u64);

        for _ in 0..3000 {
            let prev_a = a_add_eq.clone();
            let prev_b = b_add_eq.clone();
            b_add_eq.add_assign(&a_add_eq);
            let mut reversing_b = b_add_eq.clone();
            reversing_b -= &prev_b;
            assert_eq!(prev_a, reversing_b, "a not equal");
            a_add_eq = prev_b;
        }
    }

    #[test]
    fn sub_assign_reverses_neg_fib_step() -> () {
        let mut a_add_eq = BigInt::from(-1);
        let mut b_add_eq = BigInt::from(-1);

        for _ in 0..3000 {
            let prev_a = a_add_eq.clone();
            let prev_b = b_add_eq.clone();
            b_add_eq.add_assign(&a_add_eq);
            let mut reversing_b = b_add_eq.clone();
            reversing_b -= &prev_b;
            assert_eq!(prev_a, reversing_b, "a not equal");
            a_add_eq = prev_b;
        }
    }

    #[test]
    /**
     * Test whether (&BigInt as Mul<&BigInt>)::mul
     * Can calculate (100!)^2, checking it against
     * (&BigInt as Mul<u32>) by calculating the same number with
     * small multiplicands.
     */
    fn mul_factorial_square() -> () {
        // Uses (&BigUInt).mul(&BigUInt)
        let fact_square_1 = {
            let mut factorial = BigInt::from(1);

            for factor in 2u32..=50 {
                factorial = &factorial * factor;
            }
            &factorial * &factorial
        };

        // Performs simpler u32 multiplication
        let fact_square_2 = {
            let mut factorial_sq = BigInt::from(1);

            for factor in 2u32..=50 {
                factorial_sq = &factorial_sq * (factor * factor);
            }

            factorial_sq
        };

        assert_eq!(fact_square_1, fact_square_2);
    }
}
