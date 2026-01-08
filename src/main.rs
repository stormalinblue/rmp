use bignum::bigint::BigInt;
use bignum::biguint::BigUInt;

fn main() {
    let a = BigUInt::from(0x36u64);
    let b = BigUInt::from(0x63u64);
    let d = BigInt::from(b.clone());

    println!("{:?}", &a + &b);
    println!("{:?}", &b - &a);
    println!("{:?} {:?}", &d, -(d.clone()))
}
