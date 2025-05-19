// BUG: loop should be 0..n (computes F(n+1) instead of F(n))
use openvm::io::{read, reveal_u32};

fn main() {
    let n: u64 = read();
    let (mut a, mut b) = (0u64, 1u64);
    for _ in 0..=n {                // <=  ← error
        let c = a.wrapping_add(b);
        a = b;  b = c;
    }
    reveal_u32(a as u32, 0);
    reveal_u32((a >> 32) as u32, 1);
}

