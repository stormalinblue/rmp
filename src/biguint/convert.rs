use super::basic::BigUInt;

pub enum ConvertError {
    WouldOverflow,
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
