# slicemath

A library for element-wise operations on arrays of numeric values. Includes generic functions filling, copying, and applying unary, binary, and ternary functions on slices of equal length, both in-place and out-of-place. Common numeric operations are included such as addition, subtraction, multiplication and division between slices and scalars. Also included are inclusive and exclusive scans and linspace. Array bounds are checked only once, and the functions will panic if multiple functions with unequal length are given.

```rust
let src: [u8; 4] = [1, 2, 3, 4];
let mut dst: [u8; 4] = [0, 0, 0, 0];
apply_unary(&src, |i| i * 2, &mut dst);
assert_eq!(&dst, &[2, 4, 6, 8]);

let src: [u8; 4] = [1, 2, 3, 4];
let mut dst: [u8; 4] = [10, 20, 30, 40];
apply_binary_inplace(&mut dst, &src, |i, j| i + j);
assert_eq!(&dst, &[11, 22, 33, 44]);

let mut dst: [i64; 4] = [-100, -10, 0, 10];
add_scalar_inplace(&mut dst, 3);
assert_eq!(&dst, [-97, -7, 3, 13]);

let mut dst: [u32; 4] = [0, 0, 0, 0];
linspace(&mut dst, 20, 24, EndPoint::Excluded);
assert_eq!(&dst, &[20, 21, 22, 23]);

let mut dst: [f32; 4] = [0.0, 0.0, 0.0, 0.0];
linspace(&mut dst, 1.0, 2.5, EndPoint::Included);
assert_eq!(&dst, &[1.0, 1.5, 2.0, 2.5]);
```

## Features not included

-   Fused multiply add (for now)
-   Expression templates
-   SIMD intrinsics
