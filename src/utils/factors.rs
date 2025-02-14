use crate::utils::primes::Primes;
use rug::ops::Pow;
use rug::rand::RandState;
use rug::{Complete, Float, Integer};
use std::collections::BTreeMap;

/// Computes the prime factorization of a number.
///
/// Returns a map where keys are prime factors and values are their
/// exponents.
///
/// # Arguments
///
/// * `n` - The number to factorize
///
/// # Examples
///
/// ```
/// let f = factors(12);
/// assert_eq!(f.get(&2), Some(&2)); // 12 = 2^2 * 3^1
/// assert_eq!(f.get(&3), Some(&1));
/// ```
///
/// # Special Cases
///
/// * Returns {0: 1} for input 0
/// * Returns {1: 1} for input 1
#[allow(clippy::missing_panics_doc)]
#[allow(clippy::cast_possible_truncation)]
#[must_use]
pub fn trial_division(mut n: i64) -> BTreeMap<i64, u32>
{
    let mut factors = BTreeMap::new();

    if n < 0
    {
        factors.insert(-1, 1);
        n = -n;
    }

    if n == 0 || n == 1
    {
        factors.insert(n, 1);
        return factors;
    }

    for prime in Primes::new(usize::try_from(n.isqrt()).expect("Couldn't truncate i64 to usize"))
        .iter()
        .map(|p| i64::try_from(p).expect("Prime too large for i64"))
    {
        while n % prime == 0
        {
            *factors.entry(prime).or_insert(0) += 1;
            n /= prime;
        }
    }

    if n > 1
    {
        factors.insert(n, 1);
    }

    factors
}

/// Find the number of trailing zeros in a number in its binary representation.
fn trailing_zeros(num: &Integer) -> u32
{
    // (num & -num).trailing_zeros() in Rust.
    // f64's mantissa is 53 bits long.
    Float::with_val(53, num & (-num.clone()))
        .log2()
        .to_u32_saturating()
        .expect("float too big for u32")
}

/// Find the prime factors of a number using Pollard's rho algorithm
/// repeatedly.
///
/// # Arguments
///
/// * `n` - The number to factorize.
///
/// # Returns
/// A map of prime factors and their frequencies.
///
/// # Warning
/// Since the algorithm is probabilistic, it may not always return the
/// correct factors or may not factorize the number or some factors at all.
#[allow(clippy::many_single_char_names)]
#[must_use]
pub fn pollards_rho(num: &Integer) -> BTreeMap<Integer, u32>
{
    let mut factors = BTreeMap::new();
    let mut num = num.clone();

    if num == 0 || num == 1
    {
        return factors;
    }

    if num.is_negative()
    {
        factors.insert(Integer::NEG_ONE.clone(), 1);
        num = -num;
    }

    // Add the counts of 2 if n is even.
    if num.is_even()
    {
        // Traliling zeros.
        let zeros = trailing_zeros(&num);
        *factors.entry(Integer::from(2)).or_insert(0) += zeros;
        num >>= zeros; // n /= 2^k

        if num == 1
        {
            return factors;
        }
    }

    let mut rng = RandState::new();
    // Select an x_0 uniformly at random from [2, n - 1] -> [0, n - 3].
    //
    // Floyd's cycle-finding algorithm.
    // x => x_i
    // y => x_i+1
    let mut x: Integer = {
        let mut x = Integer::from(&num - 3).abs();

        // random_below_mut panics if x is zero.
        if x.is_zero()
        {
            x += 1;
        }

        x.random_below_mut(&mut rng);
        x + 2
    };
    let mut y: Integer = x.clone();
    let mut d: Integer = Integer::ONE.clone();
    let f = |z: &Integer| (z.pow(2).complete() + 1) % &num;

    while d == *Integer::ONE
    {
        x = f(&x);
        y = f(&f(&y));

        d = (&x - &y).complete().gcd(&num);
    }

    if d == num
    {
        *factors.entry(num).or_insert(0) += 1;
    }
    // Look for other factors.
    else
    {
        for (factor, freq) in pollards_rho(&d)
        {
            *factors.entry(factor).or_insert(0) += freq;
        }

        for (factor, freq) in pollards_rho(&(num / d))
        {
            *factors.entry(factor).or_insert(0) += freq;
        }
    }

    factors
}

/// Calculates the number of divisors of a given number.
///
/// Uses the prime factorization to compute the total number of divisors.
/// For a number N = p1^a * p2^b * p3^c, the number of divisors is
/// (a+1)(b+1)(c+1).
///
/// # Arguments
///
/// * `n` - The number to find divisors for
///
/// # Examples
/// ```
/// assert_eq!(divisor_num(12), 6); // 1, 2, 3, 4, 6, 12
/// ```
#[must_use]
pub fn divisor_num(n: i64) -> u32
{
    if n == 0 || n == 1
    {
        return 1;
    }

    trial_division(n)
        .values()
        .map(|&v| v + 1)
        .product()
}

/// Computes Euler's totient function φ(n).
///
/// Calculates the count of numbers up to n that are coprime to n.
/// Uses the multiplicative property of the totient function based on prime
/// factorization.
///
/// # Arguments
///
/// * `n` - The number to compute the totient for
///
/// # Examples
///
/// ```
/// assert_eq!(totient(12), 4); // 1, 5, 7, 11 are coprime to 12
/// ```
///
/// # Special Cases
///
/// * Returns 0 for input 0
/// * Returns 1 for input 1
#[must_use]
pub fn totient(n: i64) -> i64
{
    // Special case.
    if n <= 1
    {
        return n;
    }

    // https://mathworld.wolfram.com/TotientFunction.html
    trial_division(n)
        .iter()
        .fold(n, |acc, (&prime, &_power)| {
            // Apply the formula: n * (1 - 1/p) for each prime factor.
            // 1 - 1/p = p-1/p
            acc * (prime - 1) / prime
        })
}

#[cfg(test)]
mod tests
{
    use super::*;

    #[test]
    fn test_trial_division()
    {
        let f = trial_division(0);
        assert_eq!(f.get(&0), Some(&1));

        let f = trial_division(1);
        assert_eq!(f.get(&1), Some(&1));

        let f = trial_division(12);
        assert_eq!(f.get(&2), Some(&2));
        assert_eq!(f.get(&3), Some(&1));

        let f = trial_division(720);
        assert_eq!(f.get(&2), Some(&4));
        assert_eq!(f.get(&3), Some(&2));
        assert_eq!(f.get(&5), Some(&1));
    }

    #[test]
    fn test_divisor_num()
    {
        assert_eq!(divisor_num(0), 1);
        assert_eq!(divisor_num(1), 1);
        assert_eq!(divisor_num(6), 4);
        assert_eq!(divisor_num(12), 6);
        assert_eq!(divisor_num(28), 6);
        assert_eq!(divisor_num(720), 30);
    }

    #[test]
    fn test_totient()
    {
        assert_eq!(totient(0), 0);
        assert_eq!(totient(1), 1);
        assert_eq!(totient(12), 4);
        assert_eq!(totient(36), 12);
        assert_eq!(totient(43), 42);
    }

    #[test]
    fn test_trailing_zeros()
    {
        assert_eq!(trailing_zeros(&Integer::from(0)), 0);
        assert_eq!(trailing_zeros(&Integer::from(1)), 0);
        assert_eq!(trailing_zeros(&Integer::from(2)), 1);
        assert_eq!(trailing_zeros(&Integer::from(4)), 2);
        assert_eq!(trailing_zeros(&Integer::from(8)), 3);
        assert_eq!(trailing_zeros(&Integer::from(16)), 4);
        assert_eq!(trailing_zeros(&Integer::from(32)), 5);
        assert_eq!(trailing_zeros(&Integer::from(48)), 4);
        assert_eq!(trailing_zeros(&Integer::from(720)), 4);
        assert_eq!(trailing_zeros(&Integer::from(1024)), 10);
    }

    #[test]
    fn test_pollards_rho()
    {
        let f = pollards_rho(&Integer::from(0));
        assert_eq!(f.len(), 0);

        let f = pollards_rho(&Integer::from(1));
        assert_eq!(f.len(), 0);

        let f = pollards_rho(&Integer::from(12));
        assert_eq!(f.get(&Integer::from(2)), Some(&2));
        assert_eq!(f.get(&Integer::from(3)), Some(&1));

        let f = pollards_rho(&Integer::from(720));
        assert_eq!(f.get(&Integer::from(2)), Some(&4));
        assert_eq!(f.get(&Integer::from(3)), Some(&2));
        assert_eq!(f.get(&Integer::from(5)), Some(&1));

        let f = pollards_rho(&Integer::from(171));
        assert_eq!(f.get(&Integer::from(3)), Some(&2));
        assert_eq!(f.get(&Integer::from(19)), Some(&1));
    }

    #[test]
    #[should_panic]
    fn test_pollards_rho_not_working()
    {
        let f = pollards_rho(&Integer::from(25));
        assert_eq!(f.get(&Integer::from(5)), Some(&2));
    }
}
