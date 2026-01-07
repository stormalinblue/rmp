use bignum::biguint::BigUInt;

fn main() {
    let a = BigUInt::from(0x36u64);
    let b = BigUInt::from(0x63u64);

    println!("{:?}", &a + &b);
}
