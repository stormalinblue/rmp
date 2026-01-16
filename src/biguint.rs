use std::cmp::{self, Ord, Ordering};
use std::fmt::Debug;
use std::ops::{Add, AddAssign, Sub};

#[derive(Clone)]
pub struct BigUInt {
    limbs: Vec<u64>,
}

impl BigUInt {
    fn zero() -> Self {
        BigUInt { limbs: vec![] }
    }

    pub fn is_zero(&self) -> bool {
        return self.limbs.len() == 0;
    }

    pub unsafe fn sub_unchecked(&self, other: &Self) -> Self {
        let mut new_limbs = Vec::with_capacity(cmp::max(self.limbs.len(), other.limbs.len()));
        let mut carry: bool = true;

        for index in 0..cmp::max(self.limbs.len(), other.limbs.len()) {
            let left_limb = self.limbs.get(index).copied().unwrap_or(0);
            let right_limb = !other.limbs.get(index).copied().unwrap_or(0);

            let (intermediate_val, first_overflow) = left_limb.overflowing_add(right_limb);
            let next_val = if carry {
                let (final_val, second_overflow) = intermediate_val.overflowing_add(1);
                carry = first_overflow | second_overflow;
                final_val
            } else {
                carry = first_overflow;
                intermediate_val
            };

            if next_val == 0 {
                continue;
            }

            while new_limbs.len() + 1 < index {
                new_limbs.push(0);
            }
            new_limbs.push(next_val)
        }

        BigUInt { limbs: new_limbs }
    }
}

impl From<u32> for BigUInt {
    fn from(n: u32) -> BigUInt {
        BigUInt {
            limbs: vec![n as u64],
        }
    }
}

impl From<u64> for BigUInt {
    fn from(n: u64) -> BigUInt {
        BigUInt {
            limbs: vec![n as u64],
        }
    }
}

pub enum ConvertError {
    WouldOverflow,
}

impl TryFrom<&BigUInt> for u64 {
    type Error = ConvertError;

    fn try_from(n: &BigUInt) -> Result<u64, ConvertError> {
        match n.limbs.len() {
            0 => Ok(0),
            1 => Ok(n.limbs[0]),
            _ => Err(ConvertError::WouldOverflow),
        }
    }
}

impl PartialEq<BigUInt> for BigUInt {
    fn eq(&self, other: &BigUInt) -> bool {
        self.limbs == other.limbs
    }
}

impl Eq for BigUInt {}

impl PartialOrd for BigUInt {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BigUInt {
    fn cmp(&self, other: &Self) -> Ordering {
        let ord = self.limbs.len().cmp(&other.limbs.len());
        if ord == cmp::Ordering::Equal {
            self.limbs.cmp(&other.limbs)
        } else {
            ord
        }
    }
}

impl Add<&BigUInt> for &BigUInt {
    type Output = BigUInt;

    fn add(self: Self, other: &BigUInt) -> BigUInt {
        let max_limbs = cmp::max(self.limbs.len(), other.limbs.len());
        let mut new_limbs = Vec::with_capacity(max_limbs + 1);
        let mut carry: u64 = 0;

        let (left_limbs, right_limbs) = match self.limbs.len().cmp(&other.limbs.len()) {
            Ordering::Less => (&other.limbs, &self.limbs),
            _ => (&self.limbs, &other.limbs),
        };

        for index in 0..right_limbs.len() {
            let left_limb = self.limbs[index];
            let right_limb = other.limbs[index];

            let (intermediate_val, first_carry) = left_limb.overflowing_add(right_limb);
            let (final_val, second_carry) = intermediate_val.overflowing_add(carry);
            carry = (first_carry as u64) | (second_carry as u64);

            new_limbs.push(final_val);
        }

        for index in right_limbs.len()..max_limbs {
            let (next_val, overflow) = left_limbs[index].overflowing_add(carry);
            carry = overflow as u64;

            new_limbs.push(next_val);
        }

        if carry > 0 {
            new_limbs.push(1);
        }
        BigUInt { limbs: new_limbs }
    }
}

impl AddAssign<&BigUInt> for BigUInt {
    fn add_assign(&mut self, other: &BigUInt) {
        let max_limbs = cmp::max(self.limbs.len(), other.limbs.len());
        let target_capacity = max_limbs + 1;
        self.limbs.reserve_exact(target_capacity - self.limbs.len());
        self.limbs.resize(max_limbs, 0);
        let mut carry: u64 = 0;

        for index in 0..other.limbs.len() {
            let left_limb = self.limbs[index];
            let right_limb = other.limbs[index];

            let (intermediate_val, first_carry) = left_limb.overflowing_add(right_limb);
            let (final_val, second_carry) = intermediate_val.overflowing_add(carry);
            self.limbs[index] = final_val;

            carry = (first_carry as u64) + (second_carry as u64);
        }

        if carry > 0 {
            if other.limbs.len() < max_limbs {
                self.limbs[other.limbs.len()] += 1
            } else {
                self.limbs.push(1)
            }
        }
    }
}

impl<'a, 'b> Sub<&'b BigUInt> for &'a BigUInt {
    type Output = Option<BigUInt>;

    fn sub(self: Self, other: &BigUInt) -> Option<BigUInt> {
        match self.cmp(other) {
            cmp::Ordering::Equal => Some(BigUInt::zero()),
            cmp::Ordering::Less => None,
            _ => Some(unsafe { self.sub_unchecked(other) }),
        }
    }
}

impl Debug for BigUInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut is_first = true;
        for part in self.limbs.iter().rev() {
            let result = {
                if is_first {
                    write!(f, "0x{:x}", part)
                } else {
                    write!(f, "_{:016x}", part)
                }
            };
            if result.is_err() {
                return result;
            }
            is_first = false;
        }
        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn add_eq_corresponds_to_add_fib() -> () {
        let mut a_add = BigUInt::from(1u64);
        let mut b_add = BigUInt::from(1u64);

        let mut a_add_eq = BigUInt::from(1u64);
        let mut b_add_eq = BigUInt::from(1u64);

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
}
