use std::hint::black_box;

#[inline(never)]
fn item_count<T>(items: &[T]) -> usize {
    black_box(items.len())
}

fn main() {
    let lists: Vec<Vec<u8>> = black_box(vec![vec![1], vec![2, 3]]);
    std::process::exit(item_count(&lists) as i32);
}
