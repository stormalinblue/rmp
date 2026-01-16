use std::cmp::{self, Ord, Ordering};
use std::fmt::Debug;
use std::ops::{Add, AddAssign, Mul, ShlAssign, Sub};

#[derive(Clone)]
pub struct BigUInt {
    limbs: Vec<u64>,
}

const LIMB_SIZE_BITS: u64 = 8 * (std::mem::size_of::<u64>() as u64);

impl BigUInt {
    fn zero() -> Self {
        BigUInt { limbs: vec![] }
    }

    pub fn is_zero(&self) -> bool {
        return self.limbs.len() == 0;
    }

    pub unsafe fn sub_unchecked(&self, other: &Self) -> Self {
        let (left_limbs, right_limbs) = match self.limbs.len().cmp(&other.limbs.len()) {
            Ordering::Less => (&other.limbs, &self.limbs),
            _ => (&self.limbs, &other.limbs),
        };

        let mut new_limbs = Vec::with_capacity(left_limbs.len());
        let mut nonzero_size: usize = 0;

        let mut carry: u64 = 1;
        for index in 0..right_limbs.len() {
            let (intermediate_val, first_overflow) =
                left_limbs[index].overflowing_add(!right_limbs[index]);
            let (final_val, second_overflow) = intermediate_val.overflowing_add(carry);

            carry = (first_overflow as u64) + (second_overflow as u64);

            new_limbs.push(final_val);
            if final_val != 0 {
                nonzero_size = index + 1;
            }
        }

        for index in right_limbs.len()..left_limbs.len() {
            let (intermediate_val, first_overflow) = left_limbs[index].overflowing_add(!0u64);
            let (final_val, second_overflow) = intermediate_val.overflowing_add(carry);
            carry = (first_overflow as u64) + (second_overflow as u64);

            new_limbs.push(final_val);
            if final_val != 0 {
                nonzero_size = index + 1;
            }
        }

        unsafe {
            new_limbs.set_len(nonzero_size);
        }

        BigUInt { limbs: new_limbs }
    }

    pub unsafe fn sub_assign_unchecked(&mut self, other: &Self) {
        let mut carry: u64 = 1;
        let mut nonzero_size: usize = 0;

        for index in 0..other.limbs.len() {
            let (intermediate_val, first_overflow) =
                self.limbs[index].overflowing_add(!other.limbs[index]);
            let (final_val, second_overflow) = intermediate_val.overflowing_add(carry);

            carry = (first_overflow as u64) + (second_overflow as u64);
            self.limbs[index] = final_val;
            if final_val != 0 {
                nonzero_size = index + 1;
            }
        }

        for index in other.limbs.len()..self.limbs.len() {
            let (intermediate_val, first_overflow) = self.limbs[index].overflowing_add(!0u64);
            let (final_val, second_overflow) = intermediate_val.overflowing_add(carry);

            carry = (first_overflow as u64) + (second_overflow as u64);
            self.limbs[index] = final_val;

            if final_val != 0 {
                nonzero_size = index + 1;
            }
        }

        unsafe {
            self.limbs.set_len(nonzero_size);
        }
    }

    fn num_bits(&self) -> u64 {
        match self.limbs.len() {
            0 => 0,
            n => {
                (n as u64 - 1) * LIMB_SIZE_BITS
                    + (LIMB_SIZE_BITS - (self.limbs[n - 1].leading_zeros() as u64))
            }
        }
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
        BigUInt { limbs: vec![n] }
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
            for (left, right) in self.limbs.iter().rev().zip(other.limbs.iter().rev()) {
                match left.cmp(right) {
                    Ordering::Equal => {}
                    ord => return ord,
                }
            }
            return Ordering::Equal;
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
            let left_limb = left_limbs[index];
            let right_limb = right_limbs[index];

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
        self.limbs.reserve(target_capacity - self.limbs.len());
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

impl ShlAssign<u64> for BigUInt {
    fn shl_assign(&mut self, rhs: u64) {
        if rhs == 0 {
            return;
        }

        // println!("rhs {}", rhs);

        let old_num_bits = self.num_bits();
        let new_num_bits = old_num_bits + rhs;

        let old_num_limbs = self.limbs.len();
        let new_num_limbs = ((new_num_bits + LIMB_SIZE_BITS - 1) / LIMB_SIZE_BITS) as usize;
        self.limbs.reserve(new_num_limbs - old_num_limbs);
        unsafe { self.limbs.set_len(new_num_limbs) };

        let shift_limbs = (rhs / LIMB_SIZE_BITS) as usize;
        let shift_bits = rhs % LIMB_SIZE_BITS;

        // println!("shift limbs {} bits {}", shift_limbs, shift_bits);

        // Optimization: Use ptr::copy
        self.limbs.copy_within(0..old_num_limbs, shift_limbs);
        self.limbs[0..cmp::min(old_num_limbs, shift_limbs)].fill(0);

        // Optimization: SIMD
        for index in (shift_limbs..(shift_limbs + old_num_limbs)).rev() {
            let limb = self.limbs[index];
            let overflow = limb.unbounded_shr((LIMB_SIZE_BITS - shift_bits) as u32);
            self.limbs[index] = limb.unbounded_shl(shift_bits as u32);
            if overflow != 0 {
                self.limbs[index + 1] += overflow;
            }
        }
    }
}

impl Mul<u32> for &BigUInt {
    type Output = BigUInt;

    fn mul(self, rhs: u32) -> Self::Output {
        // Optimization: u128
        if rhs == 0 || self.is_zero() {
            return BigUInt::zero();
        }

        let rhs_num_bits: u64 = (32 - rhs.leading_zeros()) as u64;
        let lhs_num_bits = self.num_bits();

        let tot_bits = rhs_num_bits + lhs_num_bits - 1;
        let tot_limbs = ((tot_bits + LIMB_SIZE_BITS - 1) / LIMB_SIZE_BITS) as usize;

        let mut new_limbs = vec![0u64; tot_limbs];
        // println!("num new limbs {}", tot_limbs);

        let rhs_limb = rhs as u64;

        const LOWER_BONE_MASK: u64 = (1u64 << 32) - 1;

        // carry is at most 2 ** 32
        let mut carry: u64 = 0;
        for (index, limb) in self.limbs.iter().enumerate() {
            // println!("limb {} {:x}", limb, LOWER_BONE_MASK);
            let lower_bone = limb & LOWER_BONE_MASK;
            let upper_bone = limb >> 32;

            // println!("bones {} {}", lower_bone, upper_bone);

            // lower_result is at most (2 ** 64) - 2 * (2 ** 32) + 1
            let lower_result = lower_bone * rhs_limb;
            let upper_result = upper_bone * rhs_limb;

            // println!("results {} {}", lower_bone, upper_bone);

            // upper_in_current is at most 2 ** 32 - 1
            let upper_in_current = upper_result & LOWER_BONE_MASK;
            // upper_in_next is at most 2 ** 32 - 1
            let upper_in_next = upper_result >> 32;

            // println!("upper split {} {}", upper_in_current, upper_in_next);

            // lower_result + carry is at most 2 ** 64 - 2 ** 32 + 1
            // upper_in_current << 32 is at most 2 ** 64 - 2 ** 32
            // their sum is at most 2 ** 64 + new_value_bound where
            //      new_value_bound is 2 ** 64 - 2 * (2 ** 32) + 1
            // new_value is at most new_value_bound
            let (new_value, overflow) =
                (lower_result + carry).overflowing_add(upper_in_current << 32);
            new_limbs[index] = new_value;
            // carry is at most 2 ** 32 - 1 + 1 = 2 ** 32
            carry = upper_in_next + (overflow as u64);
        }

        if carry > 0 {
            new_limbs[self.limbs.len()] = carry;
        }

        return BigUInt { limbs: new_limbs };
    }
}

impl Mul<&BigUInt> for &BigUInt {
    type Output = BigUInt;

    fn mul(self, rhs: &BigUInt) -> Self::Output {
        todo!();
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
mod tests {
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

    #[test]
    fn sub_reverses_fib_step() -> () {
        let mut a_add_eq = BigUInt::from(1u64);
        let mut b_add_eq = BigUInt::from(1u64);

        for _ in 0..3000 {
            let prev_a = a_add_eq.clone();
            let prev_b = b_add_eq.clone();
            b_add_eq.add_assign(&a_add_eq);
            assert_eq!(prev_a, (&b_add_eq - &prev_b).unwrap(), "a not equal");
            a_add_eq = prev_b;
        }
    }

    #[test]
    fn sub_assign_reverses_fib_step() -> () {
        let mut a_add_eq = BigUInt::from(1u64);
        let mut b_add_eq = BigUInt::from(1u64);

        for _ in 0..3000 {
            let prev_a = a_add_eq.clone();
            let prev_b = b_add_eq.clone();
            b_add_eq.add_assign(&a_add_eq);
            let mut reversing_b = b_add_eq.clone();
            unsafe {
                reversing_b.sub_assign_unchecked(&prev_b);
            }
            assert_eq!(prev_a, reversing_b, "a not equal");
            a_add_eq = prev_b;
        }
    }

    #[test]
    fn mul_factorial_matches() -> () {
        const EXPECTED: [u64; 9] = [
            0x0u64,
            0x2735c61a00000000u64,
            0xb3b72ed2ee8b02eau64,
            0x45570cca9420c6ecu64,
            0x943a321cdf103917u64,
            0x66ef9a70eb21b5b2u64,
            0x28d54bbda40d16e9u64,
            0x964ec395dc240695u64,
            0x1b30u64,
        ];

        let mut factorial = BigUInt::from(1u32);

        for factor in 2u32..=100 {
            factorial = &factorial * factor;
        }

        assert_eq!(&EXPECTED, factorial.limbs.as_slice())
    }

    #[test]
    fn num_bits_correct() {
        assert_eq!(BigUInt::from(0b0u64).num_bits(), 0u64);
        assert_eq!(BigUInt::from(0b1u64).num_bits(), 1u64);
        assert_eq!(BigUInt::from(0b1u64 << 32).num_bits(), 33u64);

        let one = BigUInt::from(1u64);
        for shift in 0..100 {
            let mut shifted = one.clone();
            shifted <<= shift;
            assert_eq!(shifted.num_bits(), shift + 1);
        }
    }
}
