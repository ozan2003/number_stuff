use num_traits::PrimInt;
use std::mem::swap;

pub mod primes;
pub mod factors;

/// # GCD
/// Calculate the greatest common divisor of two numbers.
///
/// # Examples
/// ```
/// assert_eq!(gcd(1071, 462), 21);
/// assert_eq!(gcd(2, 3), 1);
/// ```
#[must_use]
pub fn gcd<T: PrimInt + std::ops::RemAssign>(mut a: T, mut b: T) -> T
{
    while b != T::zero()
    {
        a %= b;
        swap(&mut a, &mut b);
    }

    a
}

/// # LCM
/// Calculate the least common multiple of two numbers.
///
/// # Examples
/// ```
/// assert_eq!(lcm(21, 6), 42);
/// assert_eq!(lcm(2, 3), 6);
/// ```
#[must_use]
pub fn lcm<T: PrimInt + std::ops::RemAssign>(a: T, b: T) -> T
{
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
}