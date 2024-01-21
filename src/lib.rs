//! A library for element-wise mathematical operations on single or
//! multiple slices. In general, methods in this library will check
//! array sizes only once to confirm that all sizes match, and then
//! perform unchecked array accesses for performance. If multiple
//! arrays with mismatched sizes are passed, the methods will panic.
//!
//! Methods for common mathematical operations are provided in
//! many combinations of flavours, such as in-place and out-of-place
//! as well as binary operations on mixtures of arrays and scalars.
//! Representative examples of the nomenclature used here include
//!  - `add` to perform element-wise addition of two arrays, storing
//!    result in a third output array.
//!  - `add_inplace` to perform element-wise addition of two arrays,
//!    storing the result in one of the input arrays.
//!  - `sub_scalar` to subtract a common scalar value from each element
//!    in an array, storing the result in a separate output array.
//!  - `rdiv_scalar_inplace` to divide a scalar by each element in
//!    an array and store the result in place
//!
//! More general methods are provided as well which take simple closures
//! to be applied to each element, which allow you to perform other
//! operations not included here, such as `apply_unary`, `apply_binary_inplace`,
//! `apply_ternary`, `exclusive_scan_inplace`, etc.

#[cfg(test)]
mod test;

/// Apply the closure `f` to each element of `src` and store the result
/// in `dst`. Both slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn apply_unary<T, F: Fn(T) -> T>(src: &[T], f: F, dst: &mut [T])
where
    T: Copy,
{
    let n = src.len();
    if dst.len() != n {
        panic!("Attempted to call apply_unary() on slices of different length");
    }
    unsafe {
        // SAFETY: unsafe is used here to index into both slices without
        // bounds checking. This code is safe because the slices are
        // only indexed into over the range 0..n, and both have been
        // guaranteed by the above check to have exactly this length
        for i in 0..n {
            let s = src.get_unchecked(i);
            let d = dst.get_unchecked_mut(i);
            *d = f(*s);
        }
    }
}

/// Apply the closure `f` to each element of `dst` along with its index,
/// and store the result in `dst`.
pub fn apply_indexed_unary<T, F: Fn(usize) -> T>(dst: &mut [T], f: F) {
    let n = dst.len();
    unsafe {
        // SAFETY: unsafe is used here to index into the slice without
        // bounds checking. This code is safe because the slice is
        // only indexed into over the range 0..n, where n is the length
        // of the slice.
        for i in 0..n {
            let d = dst.get_unchecked_mut(i);
            *d = f(i);
        }
    }
}

/// Apply the closure `F` to each element in `src_dst` and store the
/// result in `src_dst`.
pub fn apply_unary_inplace<T, F: Fn(T) -> T>(src_dst: &mut [T], f: F)
where
    T: Copy,
{
    let n = src_dst.len();
    unsafe {
        // SAFETY: unsafe is used here to index into the slice without
        // bounds checking. This code is safe because the slice is
        // only indexed into over the range 0..n, where n is the length
        // of the slice.
        for i in 0..n {
            let sd = src_dst.get_unchecked_mut(i);
            *sd = f(*sd);
        }
    }
}

/// Apply the closure `f` to each corresponding pair of elements of `src1`
/// and `src2` and store the result in `dst`. All slices must have the same
/// length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn apply_binary<T, F: Fn(T, T) -> T>(src1: &[T], src2: &[T], f: F, dst: &mut [T])
where
    T: Copy,
{
    let n = src1.len();
    if src2.len() != n || dst.len() != n {
        panic!("Attempted to call apply_binary() on slices of different length");
    }
    unsafe {
        // SAFETY: unsafe is used here to index into all slices without
        // bounds checking. This code is safe because the slices are
        // only indexed into over the range 0..n, and all have been
        // guaranteed by the above check to have exactly this length
        for i in 0..n {
            let s1 = src1.get_unchecked(i);
            let s2 = src2.get_unchecked(i);
            let d = dst.get_unchecked_mut(i);
            *d = f(*s1, *s2);
        }
    }
}

/// Apply the closure `f` to each corresponding pair of elements of `src1_dst`
/// and `src2` and store the result in `src1_dst`. Both slices must have the same
/// length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn apply_binary_inplace<T, F: Fn(T, T) -> T>(src1_dst: &mut [T], src2: &[T], f: F)
where
    T: Copy,
{
    let n = src1_dst.len();
    if src2.len() != n {
        panic!("Attempted to call apply_binary_inplace() on slices of different length");
    }
    unsafe {
        // SAFETY: unsafe is used here to index into all slices without
        // bounds checking. This code is safe because the slices are
        // only indexed into over the range 0..n, and all have been
        // guaranteed by the above check to have exactly this length
        for i in 0..n {
            let s1d = src1_dst.get_unchecked_mut(i);
            let s2 = src2.get_unchecked(i);
            *s1d = f(*s1d, *s2);
        }
    }
}

/// Apply the closure `f` to each corresponding pair of elements of `src1`,
/// `src2`, and `src3`, and store the result in `dst`. All slices must have the
/// same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn apply_ternary<T, F: Fn(T, T, T) -> T>(
    src1: &[T],
    src2: &[T],
    src3: &[T],
    f: F,
    dst: &mut [T],
) where
    T: Copy,
{
    let n = src1.len();
    if src2.len() != n || src3.len() != n || dst.len() != n {
        panic!("Attempted to call apply_ternary() on slices of different length");
    }
    unsafe {
        // SAFETY: unsafe is used here to index into all slices without
        // bounds checking. This code is safe because the slices are
        // only indexed into over the range 0..n, and all have been
        // guaranteed by the above check to have exactly this length
        for i in 0..n {
            let s1 = src1.get_unchecked(i);
            let s2 = src2.get_unchecked(i);
            let s3 = src3.get_unchecked(i);
            let d = dst.get_unchecked_mut(i);
            *d = f(*s1, *s2, *s3);
        }
    }
}

/// Apply the closure `f` to each corresponding triple of elements of `src1_dst`,
/// `src2`, and `src3`, and store the result in `src1_dst`. All slices must have
/// the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn apply_ternary_inplace<T, F: Fn(T, T, T) -> T>(
    src1_dst: &mut [T],
    src2: &[T],
    src3: &[T],
    f: F,
) where
    T: Copy,
{
    let n = src1_dst.len();
    if src2.len() != n || src3.len() != n {
        panic!("Attempted to call apply_ternary_inplace() on slices of different length");
    }
    unsafe {
        // SAFETY: unsafe is used here to index into all slices without
        // bounds checking. This code is safe because the slices are
        // only indexed into over the range 0..n, and all have been
        // guaranteed by the above check to have exactly this length
        for i in 0..n {
            let s1d = src1_dst.get_unchecked_mut(i);
            let s2 = src2.get_unchecked(i);
            let s3 = src3.get_unchecked(i);
            *s1d = f(*s1d, *s2, *s3);
        }
    }
}

/// Apply the closure `f` to each neighbouring pair of elements in `src`,
/// storing the result in `dst`. The first element is copied as-is, and
/// the first result of calling `f` on the first two elements of `src`
/// in stored in the second position of `dst`.
///
/// # Panics
/// This method panics if the slices have different lengths.
///
/// # Illustration
/// ```plaintext
///     +--------+--------+--------+---
/// src |   a    |   b    |   c    | ...
///     +--------+--------+--------+---
///         |  \   /    \   /    \   /
///         |   \ /      \ /      \ /
///         |    f        f        f
///         |     \        \        \
///         |      \        \        \
///     +--------+--------+--------+---
/// dst |   a    | f(a,b) | f(b,c) | ...
///     +--------+--------+--------+---
/// ```
pub fn inclusive_scan<T, F: Fn(T, T) -> T>(src: &[T], f: F, dst: &mut [T])
where
    T: Copy,
{
    let n = src.len();
    if dst.len() != n {
        panic!("Attempted to call inclusive_scan() on slices of different length");
    }
    if n == 0 {
        return;
    }
    unsafe {
        // SAFETY: unsafe is used here to index into both slices without
        // bounds checking. This code is safe because the slices are
        // only indexed into over the range 0..n, and both have been
        // guaranteed by the above check to have exactly this length.
        // Reading both slices at index zero is safe because their
        // length has been checked above to be non-zero.
        let mut prev = *src.get_unchecked(0);
        *dst.get_unchecked_mut(0) = prev;
        for i in 1..n {
            let s = src.get_unchecked(i);
            let d = dst.get_unchecked_mut(i);
            let x = f(prev, *s);
            *d = x;
            prev = x;
        }
    }
}

/// Apply the closure `f` to each neighbouring pair of elements in `src_dst`,
/// storing the result in `src_dst`. The first element is not modified, and
/// the first result of calling `f` on the first two elements of `src_dst`
/// in stored in the second position of `src_dst`.
///
/// # Illustration
/// ```plaintext
///         +--------+--------+--------+---
/// src_dst |   a    |   b    |   c    | ...
///         +--------+--------+--------+---
///             |  \   /    \   /    \   /
///             |   \ /      \ /      \ /
///             |    f        f        f
///             |     \        \        \
///             |      \        \        \
///         +--------+--------+--------+---
/// src_dst |   a    | f(a,b) | f(b,c) | ...
///         +--------+--------+--------+---
/// ```
pub fn inclusive_scan_inplace<T, F: Fn(T, T) -> T>(src_dst: &mut [T], f: F)
where
    T: Copy,
{
    let n = src_dst.len();
    if n == 0 {
        return;
    }
    unsafe {
        // SAFETY: unsafe is used here to index into the slice without
        // bounds checking. This code is safe because the slice is
        // only indexed into over the range 0..n, where n is the length
        // of the slice.
        // Reading the slice at index zero is safe because their
        // length has been checked above to be non-zero.
        let mut prev = *src_dst.get_unchecked(0);
        for i in 1..n {
            let d = src_dst.get_unchecked_mut(i);
            let x = f(prev, *d);
            *d = x;
            prev = x;
        }
    }
}

/// Apply the closure `f` to each neighbouring pair of elements in `src`,
/// storing the result in `dst`. The first call of `f` is performed with
/// the additional previous value `prev`, which may be thought of as
/// appearing one position before the beginning of the input array, and
/// the result of this call is stored in the first position of `dst`.
///
/// # Panics
/// This method panics if the slices have different lengths.
///
/// # Illustration
/// ```plaintext
///      +-----------+--------+--------+---
///  src |     a     |   b    |   c    | ...
///      +-----------+--------+--------+---
/// prev   /       \   /    \   /    \   /
///     \ /         \ /      \ /      \ /
///      f           f        f        f
///       \           \        \        \
///        \           \        \        \
///      +-----------+--------+--------+---
///  dst | f(prev,a) | f(a,b) | f(b,c) | ...
///      +-----------+--------+--------+---
/// ```
pub fn exclusive_scan<T, F: Fn(T, T) -> T>(src: &[T], prev: T, f: F, dst: &mut [T])
where
    T: Copy,
{
    let n = src.len();
    if dst.len() != n {
        panic!("Attempted to call exclusive_scan() on slices of different length");
    }
    unsafe {
        // SAFETY: unsafe is used here to index into both slices without
        // bounds checking. This code is safe because the slices are
        // only indexed into over the range 0..n, and both have been
        // guaranteed by the above check to have exactly this length.
        let mut prev = prev;
        for i in 0..n {
            let s = src.get_unchecked(i);
            let d = dst.get_unchecked_mut(i);
            let x = f(prev, *s);
            *d = x;
            prev = x;
        }
    }
}

/// Apply the closure `f` to each neighbouring pair of elements in `src_dst`,
/// storing the result in `src_dst`. The first call of `f` is performed with
/// the additional previous value `prev`, which may be thought of as
/// appearing one position before the beginning of the input array, and
/// the result of this call is stored in the first position of `src_dst`.
///
/// # Illustration
/// ```plaintext
///         +-----------+--------+--------+---
/// src_dst |     a     |   b    |   c    | ...
///         +-----------+--------+--------+---
///    prev   /       \   /    \   /    \   /
///        \ /         \ /      \ /      \ /
///         f           f        f        f
///          \           \        \        \
///           \           \        \        \
///         +-----------+--------+--------+---
/// src_dst | f(prev,a) | f(a,b) | f(b,c) | ...
///         +-----------+--------+--------+---
/// ```
pub fn exclusive_scan_inplace<T, F: Fn(T, T) -> T>(src_dst: &mut [T], previous_value: T, f: F)
where
    T: Copy,
{
    let n = src_dst.len();
    unsafe {
        // SAFETY: unsafe is used here to index into the slice without
        // bounds checking. This code is safe because the slice is
        // only indexed into over the range 0..n, where n is the length
        // of the slice.
        // Reading the slice at index zero is safe because their
        // length has been checked above to be non-zero.
        let mut prev = previous_value;
        for i in 0..n {
            let d = src_dst.get_unchecked_mut(i);
            let x = f(prev, *d);
            *d = x;
            prev = x;
        }
    }
}

/// Copies `value` to every position of `dst`
pub fn fill<T>(dst: &mut [T], value: T)
where
    T: Copy,
{
    dst.iter_mut().for_each(|x| *x = value);
}

/// Copies each value in `src` to the corresponding position in `dst`.
/// Both slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn copy<T>(src: &[T], dst: &mut [T])
where
    T: Copy,
{
    apply_unary(src, |x| x, dst);
}

/// Negates each value in `src` and stores the results in `dst`.
/// Both slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn negate<T>(src: &[T], dst: &mut [T])
where
    T: Copy + std::ops::Neg<Output = T>,
{
    apply_unary(src, |x| -x, dst);
}

/// Negates each value in `src_dst` and stores the results in `src_dst`.
pub fn negate_inplace<T>(src_dst: &mut [T])
where
    T: Copy + std::ops::Neg<Output = T>,
{
    apply_unary_inplace(src_dst, |x| -x);
}

/// Adds all values in `src1` and `src2` element-wise and stores the results in `dst`.
/// All slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn add<T>(src1: &[T], src2: &[T], dst: &mut [T])
where
    T: Copy + std::ops::Add<T, Output = T>,
{
    apply_binary(src1, src2, |a, b| a + b, dst);
}

/// Adds all values in `src1_dst` and `src2` element-wise and stores the results in `src1_dst`.
/// All slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn add_inplace<T>(src1_dst: &mut [T], src2: &[T])
where
    T: Copy + std::ops::Add<T, Output = T>,
{
    apply_binary_inplace(src1_dst, src2, |a, b| a + b);
}

/// Adds a scalar value to each element in `src`, storing the results in `dst`.
/// All slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn add_scalar<T>(src: &[T], scalar: T, dst: &mut [T])
where
    T: Copy + std::ops::Add<T, Output = T>,
{
    apply_unary(src, |x| x + scalar, dst);
}

/// Adds a scalar value to each element in `src_dst`, storing the results in `src_dst`.
pub fn add_scalar_inplace<T>(src_dst: &mut [T], scalar: T)
where
    T: Copy + std::ops::Add<T, Output = T>,
{
    apply_unary_inplace(src_dst, |x| x + scalar);
}

/// Subtracts all values in `src2` from `src1` element-wise and stores the results in `dst`.
/// All slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn sub<T>(src1: &[T], src2: &[T], dst: &mut [T])
where
    T: Copy + std::ops::Sub<T, Output = T>,
{
    apply_binary(src1, src2, |a, b| a - b, dst);
}

/// Subtracts all values in `src2` from `src1_dst` element-wise and stores the results in `src1_dst`.
/// All slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn sub_inplace<T>(src1_dst: &mut [T], src2: &[T])
where
    T: Copy + std::ops::Sub<T, Output = T>,
{
    apply_binary_inplace(src1_dst, src2, |a, b| a - b);
}

/// Subtracts a scalar value from each element in `src`, storing the results in `dst`.
/// All slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn sub_scalar<T>(src: &[T], scalar: T, dst: &mut [T])
where
    T: Copy + std::ops::Sub<T, Output = T>,
{
    apply_unary(src, |x| x - scalar, dst);
}

/// Subtracts a scalar value from each element in `src_dst`, storing the results in `src_dst`.
pub fn sub_scalar_inplace<T>(src_dst: &mut [T], scalar: T)
where
    T: Copy + std::ops::Sub<T, Output = T>,
{
    apply_unary_inplace(src_dst, |x| x - scalar);
}

/// Subtracts each element in `src` from a scalar value, storing the results in `dst`.
/// All slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn rsub_scalar<T>(src: &[T], scalar: T, dst: &mut [T])
where
    T: Copy + std::ops::Sub<T, Output = T>,
{
    apply_unary(src, |x| scalar - x, dst);
}

/// Subtracts each element in `src_dst` from a scalar value, storing the results in `src_dst`.
pub fn rsub_scalar_inplace<T>(src_dst: &mut [T], scalar: T)
where
    T: Copy + std::ops::Sub<T, Output = T>,
{
    apply_unary_inplace(src_dst, |x| scalar - x);
}

/// Multiplies all values `src1` and `src2` element-wise and stores the results in `dst`.
/// All slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn mul<T>(src1: &[T], src2: &[T], dst: &mut [T])
where
    T: Copy + std::ops::Mul<T, Output = T>,
{
    apply_binary(src1, src2, |a, b| a * b, dst);
}

/// Multiplies all values in `src1_dst` and `src2` element-wise and stores the results in `src1_dst`.
/// All slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn mul_inplace<T>(src1_dst: &mut [T], src2: &[T])
where
    T: Copy + std::ops::Mul<T, Output = T>,
{
    apply_binary_inplace(src1_dst, src2, |a, b| a * b);
}

/// Multiplies a scalar value by each element in `src`, storing the results in `dst`.
/// All slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn mul_scalar<T>(src: &[T], scalar: T, dst: &mut [T])
where
    T: Copy + std::ops::Mul<T, Output = T>,
{
    apply_unary(src, |x| x * scalar, dst);
}

/// Multiplies a scalar value by each element in `src_dst`, storing the results in `src_dst`.
pub fn mul_scalar_inplace<T>(src_dst: &mut [T], scalar: T)
where
    T: Copy + std::ops::Mul<T, Output = T>,
{
    apply_unary_inplace(src_dst, |x| x * scalar);
}

/// Divides all values in `src1` by `src2` element-wise and stores the results in `dst`.
/// All slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn div<T>(src1: &[T], src2: &[T], dst: &mut [T])
where
    T: Copy + std::ops::Div<T, Output = T>,
{
    apply_binary(src1, src2, |a, b| a / b, dst);
}

/// Divides all values in `src1_dst` and `src2` element-wise and stores the results in `src1_dst`.
/// All slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn div_inplace<T>(src1_dst: &mut [T], src2: &[T])
where
    T: Copy + std::ops::Div<T, Output = T>,
{
    apply_binary_inplace(src1_dst, src2, |a, b| a / b);
}

/// Divides each element in `src` by a scalar value, storing the results in `dst`.
/// All slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn div_scalar<T>(src: &[T], scalar: T, dst: &mut [T])
where
    T: Copy + std::ops::Div<T, Output = T>,
{
    apply_unary(src, |x| x / scalar, dst);
}

/// Divides each element in `src_dst` by a scalar value, storing the results in `src_dst`.
pub fn div_scalar_inplace<T>(src_dst: &mut [T], scalar: T)
where
    T: Copy + std::ops::Div<T, Output = T>,
{
    apply_unary_inplace(src_dst, |x| x / scalar);
}

/// Divides a scalar value by each element in `src`, storing the results in `dst`.
/// All slices must have the same length.
///
/// # Panics
/// This method panics if the slices have different lengths.
pub fn rdiv_scalar<T>(src: &[T], scalar: T, dst: &mut [T])
where
    T: Copy + std::ops::Div<T, Output = T>,
{
    apply_unary(src, |x| scalar / x, dst);
}

/// Divides a scalar value by each element in `src_dst`, storing the results in `src_dst`.
pub fn rdiv_scalar_inplace<T>(src_dst: &mut [T], scalar: T)
where
    T: Copy + std::ops::Div<T, Output = T>,
{
    apply_unary_inplace(src_dst, |x| scalar / x);
}

#[doc(hidden)]
pub trait FromUsize {
    fn from_usize(i: usize) -> Self;
}

macro_rules! impl_from_usize {
    ($typename: ident) => {
        impl FromUsize for $typename {
            fn from_usize(i: usize) -> Self {
                i as Self
            }
        }
    };
}

impl_from_usize!(u8);
impl_from_usize!(i8);
impl_from_usize!(u16);
impl_from_usize!(i16);
impl_from_usize!(u32);
impl_from_usize!(i32);
impl_from_usize!(u64);
impl_from_usize!(i64);
impl_from_usize!(usize);
impl_from_usize!(isize);
impl_from_usize!(f32);
impl_from_usize!(f64);

/// Whether or not to include the endpoint in a range of values
///
/// See also [linspace]
pub enum EndPoint {
    /// The range includes the last value
    Included,

    /// The range does not include the last value and ends just before it
    Excluded,
}

/// Computes a linear sequence of uniformly spaced values, starting with
/// `first_value` and ending either at or just before `last_value`, depending
/// on `endpoint`. Results are written to `dst`, whose length is used to
/// determine the step size between values.
///
/// This method works for most integer and floating point values. For integers,
/// standard truncating division is used, so fractional values will be rounded
/// towards zero.
pub fn linspace<T>(dst: &mut [T], first_value: T, last_value: T, endpoint: EndPoint)
where
    T: Copy
        + std::ops::Add<T, Output = T>
        + std::ops::Sub<T, Output = T>
        + std::ops::Mul<T, Output = T>
        + std::ops::Div<T, Output = T>
        + FromUsize,
{
    let n = dst.len();
    if n == 0 {
        return;
    }
    if n == 1 {
        dst[0] = first_value;
        return;
    }
    let divisor = T::from_usize(match endpoint {
        EndPoint::Included => n - 1,
        EndPoint::Excluded => n,
    });
    let span = last_value - first_value;
    apply_indexed_unary(dst, |i| {
        let k = T::from_usize(i);
        first_value + ((span * k) / divisor)
    });
}
