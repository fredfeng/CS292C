// BUG: spec requires 63 full rounds but code uses 61
use openvm::io::{read, reveal_u32};

fn mix(state: &mut [u64; 3]) { /* omitted */ }

fn poseidon_hash(mut state: [u64; 3]) -> [u64; 3] {
    for _ in 0..61 {            // insufficient rounds
        mix(&mut state);
    }
    state
}

fn main() {
    let s0 = read(); let s1 = read(); let s2 = read();
    let out = poseidon_hash([s0, s1, s2]);
    reveal_u32(out[0] as u32, 0);
}
