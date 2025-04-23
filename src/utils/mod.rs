//! Utility functions.
//!
//! Provides utility functions for common mathematical operations.
//!
//! # Functions
//!
//! * `gcd` - Calculate the greatest common divisor of two numbers.
//! * `lcm` - Calculate the least common multiple of two numbers.
use num_traits::PrimInt;
use std::mem::swap;
use std::ops::RemAssign;

pub mod factors;
pub mod primes;
pub mod sieve;

/// Calculate the greatest common divisor of two numbers.
///
/// Uses the Euclidean algorithm to compute the GCD efficiently.
///
/// # Type Parameters
///
/// * `T` - Any primitive integer type that implements `PrimInt` and `RemAssign`
///   traits. This includes `i8`, `i16`, `i32`, `i64`, `i128`, `u8`, `u16`,
///   `u32`, `u64`, `u128`.
///
/// # Arguments
///
/// * `a` - First number
/// * `b` - Second number
///
/// # Returns
///
/// The greatest common divisor of `a` and `b`.
///
/// # Special Cases
///
/// * If either input is 0, returns the other input
/// * If both inputs are 0, returns 0
///
/// # Examples
/// ```
/// use number_stuff::utils::gcd;
///
/// assert_eq!(gcd(1071, 462), 21);
/// assert_eq!(gcd(2, 3), 1);
/// assert_eq!(gcd(0, 5), 5);
/// assert_eq!(gcd(0, 0), 0);
/// ```
#[must_use]
pub fn gcd<T: PrimInt + RemAssign>(mut a: T, mut b: T) -> T
{
    while b != T::zero()
    {
        a %= b;
        swap(&mut a, &mut b);
    }

    a
}

/// Calculate the least common multiple of two numbers.
///
/// Computes the LCM using the relation: lcm(a,b) = |a*b| / gcd(a,b).
///
/// # Type Parameters
///
/// * `T` - Any primitive integer type that implements `PrimInt` and `RemAssign`
///   traits. This includes `i8`, `i16`, `i32`, `i64`, `i128`, `u8`, `u16`,
///   `u32`, `u64`, `u128`.
///
/// # Arguments
///
/// * `a` - First number
/// * `b` - Second number
///
/// # Returns
///
/// The least common multiple of `a` and `b`.
///
/// # Special Cases
///
/// * If either input is 0, returns 0
///
/// # Examples
/// ```
/// use number_stuff::utils::lcm;
///
/// assert_eq!(lcm(21, 6), 42);
/// assert_eq!(lcm(2, 3), 6);
/// assert_eq!(lcm(0, 5), 0);
/// ```
#[must_use]
pub fn lcm<T: PrimInt + RemAssign>(a: T, b: T) -> T
{
    if a == T::zero() || b == T::zero()
    {
        return T::zero();
    }
    a / gcd(a, b) * b // Prevent overflow.
}

#[cfg(test)]
mod tests
{
    use super::*;

    #[test]
    fn test_gcd()
    {
        assert_eq!(gcd(1071, 462), 21);
        assert_eq!(gcd(2, 3), 1);
        assert_eq!(gcd(48, 18), 6);
        assert_eq!(gcd(54, 24), 6);
        assert_eq!(gcd(7, 13), 1);
        assert_eq!(gcd(28851538, 1183019), 17657);
    }

    #[test]
    fn test_lcm()
    {
        assert_eq!(lcm(21, 6), 42);
        assert_eq!(lcm(2, 3), 6);
        assert_eq!(lcm(15, 20), 60);
        assert_eq!(lcm(12, 18), 36);
        assert_eq!(lcm(7, 13), 91);
        assert_eq!(lcm(48, 180), 720);
    }

    #[test]
    fn test_lcm_with_zero()
    {
        assert_eq!(lcm(0, 5), 0);
        assert_eq!(lcm(5, 0), 0);
        assert_eq!(lcm(0, 0), 0);
    }

    #[test]
    fn test_gcd_with_zero()
    {
        assert_eq!(gcd(0, 10), 10);
        assert_eq!(gcd(10, 0), 10);
        assert_eq!(gcd(0, 0), 0);
    }
}
