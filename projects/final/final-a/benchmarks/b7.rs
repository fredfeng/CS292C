// BUG: XI should be 11 for BN-254; value 5 breaks extension-field ops
use openvm::io::read;
const XI: u64 = 5;              // incorrect

fn mul_xi(x: u64) -> u64 { x.wrapping_mul(XI) }

fn main() {
    let a: u64 = read();
    let res = mul_xi(a);
    let _ = res;
}
