use super::basic::{BigUInt, Bones, LIMB_SIZE_BITS, limb_to_bones, limb_to_bones_u32};
use std::ops::Mul;

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

        let rhs_limb = rhs as u64;

        // carry is at most 2 ** 32
        let mut carry: u64 = 0;
        for (index, limb) in self.limbs.iter().enumerate() {
            let bones = limb_to_bones(*limb);

            // lower_result is at most (2 ** 64) - 2 * (2 ** 32) + 1
            let lower_result = bones.lower * rhs_limb;
            let upper_result = bones.upper * rhs_limb;

            // upper_in_current is at most 2 ** 32 - 1
            // upper_in_next is at most 2 ** 32 - 1
            let Bones {
                upper: upper_in_next,
                lower: upper_in_current,
            } = limb_to_bones(upper_result);

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
        if self.is_zero() || rhs.is_zero() {
            return BigUInt::zero();
        }

        let mut lower_result = BigUInt::zero();
        let mut upper_result = BigUInt::zero();

        for (lshift_limbs, limb) in rhs.limbs.iter().enumerate().rev() {
            let bones = limb_to_bones_u32(*limb);

            // Optimization: Limb Shift and add
            let lower_bone_result = self * bones.lower;
            let upper_bone_result = self * bones.upper;
            lower_result.limb_lshift_add_assign(lshift_limbs, &lower_bone_result);
            upper_result.limb_lshift_add_assign(lshift_limbs, &upper_bone_result);
        }

        upper_result <<= 32;
        lower_result += &upper_result;
        lower_result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    /**
     * Test whether (&BigUInt as Mul<u32>)::mul
     * Can calculate 100!. The expected value
     * here is generated via Python's math.factorial.
     */
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
    /**
     * Test whether (&BigUInt as Mul<&BigUInt>)::mul
     * can calculate (100!)^2, checking it against
     * (&BigUInt as Mul<u32>) by calculating the same number with
     * small multiplicands.
     */
    fn mul_factorial_square() -> () {
        // Uses (&BigUInt).mul(&BigUInt)
        let fact_square_1 = {
            let mut factorial = BigUInt::from(1u32);

            for factor in 2u32..=50 {
                factorial = &factorial * factor;
            }
            &factorial * &factorial
        };

        // Performs simpler u32 multiplication
        let fact_square_2 = {
            let mut factorial_sq = BigUInt::from(1u32);

            for factor in 2u32..=50 {
                factorial_sq = &factorial_sq * (factor * factor);
            }

            factorial_sq
        };

        assert_eq!(fact_square_1, fact_square_2);
    }
}
