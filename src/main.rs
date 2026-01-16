use bignum::bigint::BigInt;
use bignum::biguint::BigUInt;

fn fibonacci(n: usize) -> BigInt {
    if n == 0 || n == 1 {
        return BigInt::from(1u64);
    }

    let mut a = BigInt::from(1u64);
    let mut b = BigInt::from(1u64);

    for _ in 2..=n {
        let next_a = b.clone();
        b += &a;
        a = next_a;
    }

    return b;
}

fn do_fibonacci() {
    for i in 0..3000 {
        println!("{:?}", fibonacci(i));
    }
}

fn main() {
    let mut factorials = Vec::<BigUInt>::new();
    let mut factorial = BigUInt::from(1u32);

    factorials.push(factorial.clone());

    for factor in 2u32..=100 {
        factorial = &factorial * factor;
        factorials.push(factorial.clone());
    }

    for (index, factorial) in factorials.iter().enumerate() {
        println!("{}: {:?}", index + 1, &factorial);
    }
}
