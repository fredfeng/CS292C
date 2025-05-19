// BUG: secret should remain private; reveal leaks it
use openvm::io::{read, reveal_u32};

fn main() {
    let secret: u64 = read();       // prover-only input
    reveal_u32(secret as u32, 0);   // information-leak vulnerability
}
