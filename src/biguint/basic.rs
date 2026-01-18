#[derive(Clone)]
pub struct BigUInt {
    pub(super) limbs: Vec<u64>,
}

#[derive(Debug)]
pub(super) struct Bones {
    pub(super) upper: u64,
    pub(super) lower: u64,
}

pub(crate) const LIMB_SIZE_BITS: u64 = 8 * (std::mem::size_of::<u64>() as u64);

pub(super) fn limb_to_bones(a: u64) -> Bones {
    const LOWER_BONE_MASK: u64 = (1u64 << 32) - 1;
    Bones {
        upper: a >> 32,
        lower: a & LOWER_BONE_MASK,
    }
}

#[derive(Debug)]
pub(super) struct BonesU32 {
    pub(super) upper: u32,
    pub(super) lower: u32,
}

pub fn limb_to_bones_u32(a: u64) -> BonesU32 {
    const LOWER_BONE_MASK: u64 = (1u64 << 32) - 1;
    BonesU32 {
        upper: (a >> 32) as u32,
        lower: (a & LOWER_BONE_MASK) as u32,
    }
}

impl BigUInt {
    pub fn zero() -> Self {
        BigUInt { limbs: vec![] }
    }

    pub fn is_zero(&self) -> bool {
        return self.limbs.len() == 0;
    }

    pub(crate) fn num_bits(&self) -> u64 {
        match self.limbs.len() {
            0 => 0,
            n => {
                (n as u64 - 1) * LIMB_SIZE_BITS
                    + (LIMB_SIZE_BITS - (self.limbs[n - 1].leading_zeros() as u64))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

    #[test]
    fn display_factorial_correct() {
        // TODO
    }
}
