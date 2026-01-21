use super::basic::{BigUInt, limb_to_bones};
use std::ops::Div;

impl BigUInt {
    fn lt_u32(&self, rhs: u32) -> bool {
        if rhs == 0 {
            return false;
        } else if self.limbs.len() == 1 && self.limbs[0] < (rhs as u64) {
            return true;
        } else {
            return false;
        }
    }

    pub fn div_mod(&self, rhs: u32) -> Option<(Self, u32)> {
        if rhs == 0 {
            return None;
        } else if self.lt_u32(rhs) {
            return Some((Self::zero(), self.limbs[0] as u32));
        }

        let divisor = rhs as u64;

        let result_num_limbs = if self.limbs[self.limbs.len() - 1] < divisor {
            self.limbs.len() - 1
        } else {
            self.limbs.len()
        };
        let mut result_limbs: Vec<u64> = Vec::with_capacity(result_num_limbs);
        let uninit_limbs = result_limbs.spare_capacity_mut();

        let mut residue: u64 = 0;
        for (lshift_limbs, limb) in self.limbs.iter().enumerate().rev() {
            let bones = limb_to_bones(*limb);

            let upper_working_copy = (residue << 32) + bones.upper;
            let upper_quot = upper_working_copy / divisor;
            residue = upper_working_copy % divisor;

            let lower_working_copy = (residue << 32) + bones.lower;
            let lower_quot = lower_working_copy / divisor;
            residue = lower_working_copy % divisor;

            if result_num_limbs > lshift_limbs {
                uninit_limbs[lshift_limbs].write((upper_quot << 32) + lower_quot);
            }
        }

        unsafe {
            result_limbs.set_len(result_num_limbs);
        }

        Some((
            Self {
                limbs: result_limbs,
            },
            residue as u32,
        ))
    }
}

impl Div<u32> for &BigUInt {
    type Output = Option<BigUInt>;
    fn div(self, rhs: u32) -> Self::Output {
        match self.div_mod(rhs) {
            None => None,
            Some((result, _)) => Some(result),
        }
    }
}
