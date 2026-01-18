use super::basic::BigUInt;
use std::cmp::{self, Ord, Ordering};

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
