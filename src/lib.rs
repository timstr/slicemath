#[cfg(test)]
mod test;

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

pub fn exclusive_scan<T, F: Fn(T, T) -> T>(src: &[T], previous_value: T, f: F, dst: &mut [T])
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
        let mut prev = previous_value;
        for i in 0..n {
            let s = src.get_unchecked(i);
            let d = dst.get_unchecked_mut(i);
            let x = f(prev, *s);
            *d = x;
            prev = x;
        }
    }
}

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

pub fn fill<T>(dst: &mut [T], value: T)
where
    T: Copy,
{
    dst.iter_mut().for_each(|x| *x = value);
}

pub fn copy<T>(src: &[T], dst: &mut [T])
where
    T: Copy,
{
    apply_unary(src, |x| x, dst);
}

pub fn negate<T>(src: &[T], dst: &mut [T])
where
    T: Copy + std::ops::Neg<Output = T>,
{
    apply_unary(src, |x| -x, dst);
}

pub fn negate_inplace<T>(src_dst: &mut [T])
where
    T: Copy + std::ops::Neg<Output = T>,
{
    apply_unary_inplace(src_dst, |x| -x);
}

pub fn add<T>(src1: &[T], src2: &[T], dst: &mut [T])
where
    T: Copy + std::ops::Add<T, Output = T>,
{
    apply_binary(src1, src2, |a, b| a + b, dst);
}

pub fn add_inplace<T>(src1_dst: &mut [T], src2: &[T])
where
    T: Copy + std::ops::Add<T, Output = T>,
{
    apply_binary_inplace(src1_dst, src2, |a, b| a + b);
}

pub fn add_scalar<T>(src: &[T], scalar: T, dst: &mut [T])
where
    T: Copy + std::ops::Add<T, Output = T>,
{
    apply_unary(src, |x| x + scalar, dst);
}

pub fn add_scalar_inplace<T>(src_dst: &mut [T], scalar: T)
where
    T: Copy + std::ops::Add<T, Output = T>,
{
    apply_unary_inplace(src_dst, |x| x + scalar);
}

pub fn sub<T>(src1: &[T], src2: &[T], dst: &mut [T])
where
    T: Copy + std::ops::Sub<T, Output = T>,
{
    apply_binary(src1, src2, |a, b| a - b, dst);
}

pub fn sub_inplace<T>(src1_dst: &mut [T], src2: &[T])
where
    T: Copy + std::ops::Sub<T, Output = T>,
{
    apply_binary_inplace(src1_dst, src2, |a, b| a - b);
}

pub fn sub_scalar<T>(src: &[T], scalar: T, dst: &mut [T])
where
    T: Copy + std::ops::Sub<T, Output = T>,
{
    apply_unary(src, |x| x - scalar, dst);
}

pub fn sub_scalar_inplace<T>(src_dst: &mut [T], scalar: T)
where
    T: Copy + std::ops::Sub<T, Output = T>,
{
    apply_unary_inplace(src_dst, |x| x - scalar);
}

pub fn rsub_scalar<T>(src: &[T], scalar: T, dst: &mut [T])
where
    T: Copy + std::ops::Sub<T, Output = T>,
{
    apply_unary(src, |x| scalar - x, dst);
}

pub fn rsub_scalar_inplace<T>(src_dst: &mut [T], scalar: T)
where
    T: Copy + std::ops::Sub<T, Output = T>,
{
    apply_unary_inplace(src_dst, |x| scalar - x);
}

pub fn mul<T>(src1: &[T], src2: &[T], dst: &mut [T])
where
    T: Copy + std::ops::Mul<T, Output = T>,
{
    apply_binary(src1, src2, |a, b| a * b, dst);
}

pub fn mul_inplace<T>(src1_dst: &mut [T], src2: &[T])
where
    T: Copy + std::ops::Mul<T, Output = T>,
{
    apply_binary_inplace(src1_dst, src2, |a, b| a * b);
}

pub fn mul_scalar<T>(src: &[T], scalar: T, dst: &mut [T])
where
    T: Copy + std::ops::Mul<T, Output = T>,
{
    apply_unary(src, |x| x * scalar, dst);
}

pub fn mul_scalar_inplace<T>(src_dst: &mut [T], scalar: T)
where
    T: Copy + std::ops::Mul<T, Output = T>,
{
    apply_unary_inplace(src_dst, |x| x * scalar);
}

pub fn div<T>(src1: &[T], src2: &[T], dst: &mut [T])
where
    T: Copy + std::ops::Div<T, Output = T>,
{
    apply_binary(src1, src2, |a, b| a / b, dst);
}

pub fn div_inplace<T>(src1_dst: &mut [T], src2: &[T])
where
    T: Copy + std::ops::Div<T, Output = T>,
{
    apply_binary_inplace(src1_dst, src2, |a, b| a / b);
}

pub fn div_scalar<T>(src: &[T], scalar: T, dst: &mut [T])
where
    T: Copy + std::ops::Div<T, Output = T>,
{
    apply_unary(src, |x| x / scalar, dst);
}

pub fn div_scalar_inplace<T>(src_dst: &mut [T], scalar: T)
where
    T: Copy + std::ops::Div<T, Output = T>,
{
    apply_unary_inplace(src_dst, |x| x / scalar);
}

pub fn rdiv_scalar<T>(src: &[T], scalar: T, dst: &mut [T])
where
    T: Copy + std::ops::Div<T, Output = T>,
{
    apply_unary(src, |x| scalar / x, dst);
}

pub fn rdiv_scalar_inplace<T>(src_dst: &mut [T], scalar: T)
where
    T: Copy + std::ops::Div<T, Output = T>,
{
    apply_unary_inplace(src_dst, |x| scalar / x);
}

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

pub enum EndPoint {
    Included,
    Excluded,
}

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
