// BUG: missing range-check on public input length ⇒ witness mismatch
use openvm::io::{read, reveal_u32};

fn main() {
    let len: u32 = read();          // prover-supplied length
    let mut acc = 0u32;
    for _ in 0..len {               // uncontrolled length
        acc = acc.wrapping_add(read());
    }
    reveal_u32(acc, 0);             // verifier assumes fixed length
}
