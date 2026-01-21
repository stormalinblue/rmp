use super::basic::BigUInt;
use std::str::FromStr;

pub enum ConvertOutNumError {
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
    type Error = ConvertOutNumError;

    fn try_from(n: &BigUInt) -> Result<u64, ConvertOutNumError> {
        match n.limbs.len() {
            0 => Ok(0),
            1 => Ok(n.limbs[0]),
            _ => Err(ConvertOutNumError::WouldOverflow),
        }
    }
}

#[derive(Debug)]
pub struct ParseBigUIntError {}

impl FromStr for BigUInt {
    type Err = ParseBigUIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Optimization: Batching

        let mut result = BigUInt::zero();
        for c in s.chars() {
            if !('0' <= c && c <= '9') {
                return Err(ParseBigUIntError {});
            } else {
                let digit = (c as u64) - ('0' as u64);
                result *= 10u32;
                result += digit;
            }
        }
        Ok(result)
    }
}

#[cfg(test)]
mod test {
    use crate::biguint::BigUInt;

    #[test]
    fn from_str_small() {
        assert_eq!("1234".parse::<BigUInt>().unwrap(), BigUInt::from(1234u64));
    }
}
