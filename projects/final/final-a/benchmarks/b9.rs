// BUG: slice::get_unchecked used without bounds proof
use openvm::io::read;

fn main() {
    let idx: usize = read() as usize;
    let data: Vec<u64> = (0..100).collect();
    // unsafe read—idx may exceed 99 causing witness ambiguity
    let _val = unsafe { *data.get_unchecked(idx) };
}
