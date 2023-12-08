use prusti_contracts::*;

#[ensures(*x == old(*y))]
#[ensures(*y == old(*x))]
fn swap(x: &mut i32, y: &mut i32) 
{
    let tmp = *x;
    *x = *y;
    *y = tmp;
}

fn client()
{
    let mut a = 16;
    let mut b = 42;
    swap(&mut a, &mut b);
    assert!(a == 42 && b == 16)
}
