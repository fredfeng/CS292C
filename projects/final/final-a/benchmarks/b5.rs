// BUG: idx not bounded ⇒ proofs may skip levels
use openvm::io::read;

const TREE_HEIGHT: u32 = 22;

fn main() {
    let idx: u32 = read();             // should enforce idx < 2^22
    let leaf: u64 = read();
    let mut hash = leaf;
    for lvl in 0..TREE_HEIGHT {
        let sibling: u64 = read();     // supplied by prover
        if (idx >> lvl) & 1 == 0 {
            hash = poseidon(hash, sibling);
        } else {
            hash = poseidon(sibling, hash);
        }
    }
    let _root = hash;
}

fn poseidon(x: u64, y: u64) -> u64 { x.wrapping_add(y) } // stub
