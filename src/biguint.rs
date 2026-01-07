use std::cmp;
use std::fmt::Debug;
use std::ops::Add;

#[derive(Clone)]
pub struct BigUInt {
    parts: Vec<u64>,
}

impl From<u64> for BigUInt {
    fn from(n: u64) -> BigUInt {
        BigUInt {
            parts: vec![n as u64],
        }
    }
}

impl PartialEq<BigUInt> for BigUInt {
    fn eq(&self, other: &BigUInt) -> bool {
        self.parts == other.parts
    }
}

impl<'a, 'b> Add<&'b BigUInt> for &'a BigUInt {
    type Output = BigUInt;

    fn add(self: Self, other: &BigUInt) -> BigUInt {
        let mut new_parts = Vec::with_capacity(cmp::max(self.parts.len(), other.parts.len()) + 1);
        let mut carry: bool = false;

        for index in 0..cmp::max(self.parts.len(), other.parts.len()) {
            let left_part = self.parts.get(index).copied().unwrap_or(0);
            let right_part = other.parts.get(index).copied().unwrap_or(0);

            let (intermediate_val, first_overflow) = left_part.overflowing_add(right_part);
            let next_val = if carry {
                let (final_val, second_overflow) = intermediate_val.overflowing_add(1);
                carry = first_overflow | second_overflow;
                final_val
            } else {
                carry = first_overflow;
                intermediate_val
            };

            new_parts.push(next_val)
        }

        if carry {
            new_parts.push(1);
        }

        BigUInt { parts: new_parts }
    }
}

impl Debug for BigUInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BigUInt(")?;

        let mut is_first = true;
        for part in self.parts.iter().rev() {
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
        write!(f, ")")?;
        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn it_adds
}
