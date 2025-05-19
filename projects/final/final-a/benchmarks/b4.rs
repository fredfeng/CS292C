// BUG: a == 0 makes exponentiation undefined; assert removed
use openvm::io::read;
const P: u64 = 0xFFFFFFFF00000001;  // example prime

fn mod_pow(mut base: u64, mut exp: u64) -> u64 {
    let mut acc = 1u64;
    while exp > 0 {
        if exp & 1 == 1 { acc = acc.wrapping_mul(base) % P; }
        base = base.wrapping_mul(base) % P;
        exp /= 2;
    }
    acc
}

fn main() {
    let a: u64 = read();
    // assert!(a != 0);             // **missing**
    let inv = mod_pow(a, P - 2);    // Fermat inverse
    let _sink = inv;                // used later
}
