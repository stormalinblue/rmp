use super::basic::BigUInt;
use std::fmt;

impl fmt::LowerHex for BigUInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_zero() {
            write!(f, "0")?;
            return Ok(());
        }

        let mut string = String::with_capacity(17 * self.limbs.len());

        let mut is_first = true;
        for part in self.limbs.iter().rev() {
            if is_first {
                string += &format!("{:x}", part);
            } else {
                string += &format!("_{:016x}", part);
            }
            is_first = false;
        }
        f.pad_integral(true, "", &string)?;
        Ok(())
    }
}

impl fmt::Display for BigUInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut working_copy = self.clone();

        if self.is_zero() {
            return write!(f, "0");
        }

        // Optimization: Divide and conquer using the 2048 algorithm
        /* Fixed point approximation of log10(2) with denominator 2 ** 32 */
        const CHARS_PER_2_TO_POWER_32_BITS: u128 = 1292913987;
        // TODO: Double check this math
        let chars_required: usize = ((CHARS_PER_2_TO_POWER_32_BITS * (self.num_bits() as u128)
            + ((1u128 << 32) - 1))
            >> 32) as usize;

        // Optimization: We don't need to initialize all these characters
        // Optimization: Figure out a streaming solution
        let mut characters: Vec<u8> = vec![0; chars_required];

        // println!("chars_required {}", chars_required);

        let mut character_index = 0;
        while !(&working_copy.is_zero()) {
            match working_copy.div_mod(10u32) {
                None => unreachable!(),
                Some((quot, rem)) => {
                    // println!("quot {:x}, rem {}", quot, rem);
                    working_copy = quot;
                    characters[chars_required - character_index - 1] = ('0' as u8) + (rem as u8);
                }
            }
            character_index += 1;
        }

        // assert_eq!(character_index, chars_required);

        // characters.truncate(character_index);

        // Optimization: We should really not need this second copy
        let string = unsafe {
            String::from_utf8_unchecked(characters[chars_required - character_index..].to_vec())
        };
        f.pad_integral(true, "", &string)?;

        Ok(())
    }
}

impl fmt::Debug for BigUInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            return f.pad_integral(true, "", &format!("{:x}", self));
        } else {
            return f.pad_integral(true, "", &format!("{}", self));
        }
    }
}
