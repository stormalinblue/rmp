use super::basic::BigUInt;
use std::cmp::{self, Ordering};
use std::ops::{Add, AddAssign, Sub};

impl BigUInt {
    pub(crate) unsafe fn sub_unchecked(&self, other: &Self) -> Self {
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

    pub(crate) unsafe fn sub_assign_unchecked(&mut self, other: &Self) {
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
}
