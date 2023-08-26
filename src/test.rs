use crate::*;

#[test]
fn test_apply_unary() {
    let src: [u8; 4] = [1, 2, 3, 4];
    let mut dst: [u8; 4] = [0, 0, 0, 0];

    apply_unary(&src, |i| i * 2, &mut dst);

    assert_eq!(&dst, &[2, 4, 6, 8]);
}

#[test]
fn test_apply_indexed_unary() {
    let mut dst: [u8; 4] = [0, 0, 0, 0];

    apply_indexed_unary(&mut dst, |i| (i as u8 + 1) * 2);

    assert_eq!(&dst, &[2, 4, 6, 8]);
}

#[test]
fn test_apply_unary_inplace() {
    let mut dst: [u8; 4] = [1, 2, 3, 4];

    apply_unary_inplace(&mut dst, |i| i * 2);

    assert_eq!(&dst, &[2, 4, 6, 8]);
}

#[test]
fn test_apply_binary() {
    let src1: [u8; 4] = [1, 2, 3, 4];
    let src2: [u8; 4] = [10, 20, 30, 40];
    let mut dst: [u8; 4] = [0, 0, 0, 0];

    apply_binary(&src1, &src2, |i, j| i + j, &mut dst);

    assert_eq!(&dst, &[11, 22, 33, 44]);
}

#[test]
fn test_apply_binary_inplace() {
    let src: [u8; 4] = [1, 2, 3, 4];
    let mut dst: [u8; 4] = [10, 20, 30, 40];

    apply_binary_inplace(&mut dst, &src, |i, j| i + j);

    assert_eq!(&dst, &[11, 22, 33, 44]);
}

#[test]
fn test_apply_ternary() {
    let src1: [u16; 4] = [1, 2, 3, 4];
    let src2: [u16; 4] = [10, 20, 30, 40];
    let src3: [u16; 4] = [100, 200, 300, 400];
    let mut dst: [u16; 4] = [0, 0, 0, 0];

    apply_ternary(&src1, &src2, &src3, |i, j, k| i + j + k, &mut dst);

    assert_eq!(&dst, &[111, 222, 333, 444]);
}

#[test]
fn test_apply_ternary_inplace() {
    let src1: [u16; 4] = [1, 2, 3, 4];
    let src2: [u16; 4] = [10, 20, 30, 40];
    let mut dst: [u16; 4] = [100, 200, 300, 400];

    apply_ternary_inplace(&mut dst, &src1, &src2, |i, j, k| i + j + k);

    assert_eq!(&dst, &[111, 222, 333, 444]);
}

#[test]
fn test_inclusive_scan() {
    let src: [u16; 4] = [1, 2, 3, 4];
    let mut dst: [u16; 4] = [0, 0, 0, 0];

    inclusive_scan(&src, |acc, i| acc + i, &mut dst);

    assert_eq!(&dst, &[1, 3, 6, 10]);
}

#[test]
fn test_inclusive_scan_inplace() {
    let mut dst: [u16; 4] = [1, 2, 3, 4];

    inclusive_scan_inplace(&mut dst, |acc, i| acc + i);

    assert_eq!(&dst, &[1, 3, 6, 10]);
}

#[test]
fn test_exclusive_scan() {
    let src: [u16; 4] = [1, 2, 3, 4];
    let mut dst: [u16; 4] = [0, 0, 0, 0];

    exclusive_scan(&src, 1, |acc, i| acc + i, &mut dst);

    assert_eq!(&dst, &[2, 4, 7, 11]);
}

#[test]
fn test_exclusive_scan_inplace() {
    let mut dst: [u16; 4] = [1, 2, 3, 4];

    exclusive_scan_inplace(&mut dst, 1, |acc, i| acc + i);

    assert_eq!(&dst, &[2, 4, 7, 11]);
}

// TODO: test other helper functions?

#[test]
fn test_linspace_integer_endpoint_included() {
    let mut dst: [u32; 4] = [0, 0, 0, 0];

    linspace(&mut dst, 10, 16, EndPoint::Included);

    assert_eq!(&dst, &[10, 12, 14, 16]);
}

#[test]
fn test_linspace_integer_endpoint_excluded() {
    let mut dst: [u32; 4] = [0, 0, 0, 0];

    linspace(&mut dst, 20, 24, EndPoint::Excluded);

    assert_eq!(&dst, &[20, 21, 22, 23]);
}

#[test]
fn test_linspace_float_endpoint_included() {
    let mut dst: [f32; 4] = [0.0, 0.0, 0.0, 0.0];

    linspace(&mut dst, 1.0, 2.5, EndPoint::Included);

    assert_eq!(&dst, &[1.0, 1.5, 2.0, 2.5]);
}

#[test]
fn test_linspace_float_endpoint_excluded() {
    let mut dst: [f32; 4] = [0.0, 0.0, 0.0, 0.0];

    linspace(&mut dst, 1.0, 2.0, EndPoint::Excluded);

    assert_eq!(&dst, &[1.0, 1.25, 1.5, 1.75]);
}
