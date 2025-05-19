// BUG: missing .wrapping_add or range assertion ⇒ overflow mismatch
use openvm::io::{read, reveal_u32};

fn main() {
    let x: u64 = read();
    let y: u64 = read();
    let z = x + y;                  // unchecked
    reveal_u32(z as u32, 0);
    reveal_u32((z >> 32) as u32, 1);
}
