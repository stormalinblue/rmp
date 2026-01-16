use std::cmp::{self, Ord, Ordering};
use std::fmt::Debug;
use std::ops::{Add, Sub};

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

impl<'a, 'b> Add<&'b BigUInt> for &'a BigUInt {
    type Output = BigUInt;

    fn add(self: Self, other: &BigUInt) -> BigUInt {
        let mut new_limbs = Vec::with_capacity(cmp::max(self.limbs.len(), other.limbs.len()) + 1);
        let mut carry: bool = false;

        for index in 0..cmp::max(self.limbs.len(), other.limbs.len()) {
            let left_limb = self.limbs.get(index).copied().unwrap_or(0);
            let right_limb = other.limbs.get(index).copied().unwrap_or(0);

            let (intermediate_val, first_overflow) = left_limb.overflowing_add(right_limb);
            let next_val = if carry {
                let (final_val, second_overflow) = intermediate_val.overflowing_add(1);
                carry = first_overflow | second_overflow;
                final_val
            } else {
                carry = first_overflow;
                intermediate_val
            };

            new_limbs.push(next_val)
        }

        if carry {
            new_limbs.push(1);
        }

        BigUInt { limbs: new_limbs }
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
                    write!(f, ".{:016x}", part)
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
    fn it_adds() -> () {}
}
