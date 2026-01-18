use super::basic::{BigUInt, LIMB_SIZE_BITS};
use std::cmp;
use std::ops::ShlAssign;

impl ShlAssign<u64> for BigUInt {
    fn shl_assign(&mut self, rhs: u64) {
        if rhs == 0 || self.is_zero() {
            return;
        }

        let old_num_bits = self.num_bits();
        let new_num_bits = old_num_bits + rhs;

        let old_num_limbs = self.limbs.len();
        let new_num_limbs = ((new_num_bits + LIMB_SIZE_BITS - 1) / LIMB_SIZE_BITS) as usize;
        self.limbs.reserve(new_num_limbs - old_num_limbs);
        // SAFETY: Perhaps we are stepping into UB
        // All of these bytes should be written to before we read them
        unsafe { self.limbs.set_len(new_num_limbs) };

        let shift_limbs = (rhs / LIMB_SIZE_BITS) as usize;
        let shift_bits = rhs % LIMB_SIZE_BITS;

        // Optimization: Use ptr::copy
        self.limbs.copy_within(0..old_num_limbs, shift_limbs);
        self.limbs[0..cmp::min(old_num_limbs, shift_limbs)].fill(0);

        /*
         * Optimize for the internally common case of shifting by
         * a multiple of limb size (perhaps should provide
         * a dedicated routine).
         */
        if shift_bits == 0 {
            return;
        }

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
