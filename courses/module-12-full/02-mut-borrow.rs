use prusti_contracts::*;

#[ensures(*x == old(*y))]
#[ensures(*y == old(*x))]
fn swap(x: &mut i32, y: &mut i32) {
    let tmp = *x;
    *x = *y;
    *y = tmp;
}

fn main() {
    let mut a = 19;
    let mut b = 23;
    let x = &mut a;
    let y = &mut b;

    swap(x, y);

    // a = 42; // FAILS

    assert!(*x == 23 && b == 19);
    
    // swap(&mut a, &mut a); // FAILS
}