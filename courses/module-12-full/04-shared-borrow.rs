fn sum(p: &i32, q: &i32) -> i32 {
    p + q
}

fn main() {
    let mut x = 4;
    let b = &x;
    let c = &x;

    // x = 7 // FAILS
    x = sum(b, c);
}