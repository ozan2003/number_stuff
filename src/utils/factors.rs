//! Integer factorization services.
//!
//! Provides functions to factorize integers into their prime factors.
//!
//! # Functions
//!
//! * `trial_division` - Factorize using trial division.
//! * `pollards_rho` - Factorize using Pollard's rho algorithm.
//! * `divisor_num` - Calculate the number of divisors of a number.
//! * `totient` - Calculate Euler's totient function.
use std::collections::BTreeMap;

use malachite::base::num::arithmetic::traits::{
    Abs as _,
    Gcd as _,
    Parity as _,
    Pow as _,
};
use malachite::base::num::logic::traits::SignificantBits as _;
use malachite::{Integer, Natural};

use crate::utils::primes::is_prime;
use crate::utils::sieve::Primes;

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
/// let f = trial_division(12);
/// assert_eq!(f.get(&2), Some(&2)); // 12 = 2^2 * 3^1
/// assert_eq!(f.get(&3), Some(&1));
/// ```
///
/// # Special Cases
///
/// * Returns {0: 1} for input 0
/// * Returns {1: 1} for input 1
#[expect(
    clippy::missing_panics_doc,
    reason = "panics are guarded internal conversions that cannot fail for \
              valid inputs"
)]
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

    let primes = Primes::new(
        usize::try_from(n.isqrt()).expect("Couldn't truncate i64 to usize"),
    );

    for prime in primes
        .into_iter()
        .map(|p| i64::try_from(p).expect("Prime too large for i64"))
    {
        while n % prime == 0
        {
            factors
                .entry(prime)
                .and_modify(|v| *v += 1)
                .or_insert(1);
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
///
/// Determines how many times a number is divisible by 2 by counting the
/// consecutive zero bits from the least significant bit.
///
/// # Arguments
///
/// * `num` - The integer to analyze
///
/// # Returns
///
/// The number of trailing zeros in the binary representation of `num`.
///
/// Returns 0 for the special case of 0.
///
/// # Examples
///
/// ```
/// use number_stuff::utils::factors::trailing_zeros;
/// use malachite::Integer;
///
/// assert_eq!(trailing_zeros(&Integer::from(8)), 3);  // 8 = 1000₂, has 3 trailing zeros
/// assert_eq!(trailing_zeros(&Integer::from(12)), 2); // 12 = 1100₂, has 2 trailing zeros
/// assert_eq!(trailing_zeros(&Integer::from(0)), 0);  // Special case
/// ```
fn trailing_zeros(num: &Integer) -> u32
{
    if *num == 0
    {
        return 0; // Special case for zero.
    }

    // Find the position of the lowest set bit.
    u32::try_from(
        num.trailing_zeros()
            .expect("Nonzero integer has trailing zeros"),
    )
    .expect("Trailing zeros fit in u32")
}

/// Find the prime factors of a number using Pollard's rho algorithm
/// repeatedly.
///
/// This function implements Pollard's rho algorithm, a probabilistic
/// factorization method that is particularly efficient for finding small
/// factors of large numbers. The function handles the factorization recursively
/// until all factors are found.
///
/// # Arguments
///
/// * `num` - The number to factorize.
///
/// # Returns
///
/// A map of prime factors and their exponents.
///
/// For inputs 0 and 1, returns an
/// empty map. For negative inputs, includes -1 as a factor with exponent 1.
///
/// # Examples
///
/// ```
/// use number_stuff::utils::factors::pollards_rho;
/// use malachite::Integer;
/// use std::collections::BTreeMap;
///
/// // Factorize 12 = 2^2 * 3^1
/// let factors = pollards_rho(&Integer::from(12));
/// assert_eq!(factors.get(&Integer::from(2)), Some(&2));
/// assert_eq!(factors.get(&Integer::from(3)), Some(&1));
///
/// // Special cases
/// assert_eq!(pollards_rho(&Integer::from(0)).len(), 0);
/// assert_eq!(pollards_rho(&Integer::from(1)).len(), 0);
/// ```
///
/// # Warning
/// Since the algorithm is probabilistic, it may not always find all factors
/// for very large or specially constructed numbers.
#[expect(
    clippy::missing_panics_doc,
    reason = "panics are guarded internal conversions that cannot fail for \
              valid inputs"
)]
#[expect(clippy::many_single_char_names, reason = "its all math stuff")]
#[must_use]
pub fn pollards_rho(num: &Integer) -> BTreeMap<Integer, u32>
{
    const MAX_ITERATIONS: i32 = 100; // safety guard to prevent infinite loops.

    let mut factors = BTreeMap::new();
    let mut num = num.clone();

    if num == 0 || num == 1
    {
        return factors;
    }

    if num < 0
    {
        factors.insert(Integer::from(-1), 1);
        num = -num;
    }

    // Add the counts of 2 if n is even.
    if num.even()
    {
        let zeros = trailing_zeros(&num);
        factors
            .entry(Integer::from(2))
            .and_modify(|v| *v += zeros)
            .or_insert(zeros);

        num >>= u64::from(zeros); // n /= 2^k

        if num == 1
        {
            return factors;
        }
    }

    // Early check for small primes.
    if is_prime(&num)
    {
        factors
            .entry(num)
            .and_modify(|v| *v += 1)
            .or_insert(1);
        return factors;
    }

    let mut rng = urandom::new();
    // `num` is now odd, composite and at least 9; keep a Natural view for gcd.
    let num_nat = Natural::try_from(&num).expect("`num` is positive");
    let max_attempts = 3;

    for attempt in 1..=max_attempts
    {
        // Vary the polynomial function with each attempt.
        let c = Integer::from(attempt);
        // f(z) = z^2 + c mod n.
        let f = |z: &Integer| (z.pow(2u64) + &c) % &num;

        // Select an x_0 uniformly at random from [2, n - 1] -> [0, n - 3].
        //
        // Floyd's cycle-finding algorithm.
        // x => x_i
        // y => x_i+1
        let mut x: Integer = {
            // Generate enough random bits to cover the range, then reduce
            // modulo `num - 3` to land in [2, n - 1).
            let mut raw = Integer::from(0u64);
            for _ in 0..num.significant_bits().div_ceil(64)
            {
                raw <<= 64u64;
                raw += Integer::from(rng.next::<u64>());
            }
            raw % (&num - &Integer::from(3)) + &Integer::from(2)
        };
        let mut y = x.clone();
        let mut d = Integer::from(1);

        // Floyd's cycle finding with optimizations.
        let mut iterations = 0;

        while d == 1 && iterations < MAX_ITERATIONS
        {
            x = f(&x);
            y = f(&f(&y));

            // gcd being 1 indicates |x - y| and n are coprime.
            let diff = (&x - &y).abs();
            d = Integer::from(
                (&Natural::try_from(&diff).expect("`diff` is nonnegative"))
                    .gcd(&num_nat),
            );
            iterations += 1;
        }

        if d != 1 && d != num
        {
            // Found a proper factor, look for others.
            // If d = n, we haven't actually factorized anything useful
            for (factor, freq) in pollards_rho(&d)
            {
                factors
                    .entry(factor)
                    .and_modify(|v| *v += freq)
                    .or_insert(freq);
            }
            for (factor, freq) in pollards_rho(&(num / &d))
            {
                factors
                    .entry(factor)
                    .and_modify(|v| *v += freq)
                    .or_insert(freq);
            }

            return factors;
        }
    }

    // If we get here, consider it prime (or give up).
    factors
        .entry(num)
        .and_modify(|v| *v += 1)
        .or_insert(1);

    factors
}

/// Calculates the number of divisors of a given number.
///
/// Uses the prime factorization to compute the total number of divisors.
///
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
///
/// # Panics
/// Panics if the calculation results in overflow.
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
            acc.checked_mul(prime - 1)
                .and_then(|v| v.checked_div(prime))
                .expect("Overflow in calculation.")
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

        let f = pollards_rho(&Integer::from(125));
        assert_eq!(f.get(&Integer::from(5)), Some(&3));

        // Large composite number with medium-sized factors.
        let f = pollards_rho(&Integer::from(1_234_567_890_123_456_789_u64));
        assert_eq!(f.get(&Integer::from(3)), Some(&2));
        assert_eq!(f.get(&Integer::from(101)), Some(&1));
        assert_eq!(f.get(&Integer::from(3541)), Some(&1));
        assert_eq!(f.get(&Integer::from(3_607)), Some(&1));
        assert_eq!(f.get(&Integer::from(3_803)), Some(&1));
        assert_eq!(f.get(&Integer::from(27_961)), Some(&1));

        let big_prime = Integer::from(18_446_744_073_709_551_557_u64);
        let f = pollards_rho(&big_prime);
        assert_eq!(f.len(), 1);
    }

    #[test]
    #[should_panic = "Pollard's rho algorithm is probabilistic and may fail on \
                      certain inputs."]
    fn test_pollards_rho_not_working()
    {
        let big_number =
            Integer::from(10_000_000_000_006_800_000_000_001_147_u128);
        let f = pollards_rho(&big_number);
        assert_eq!(f.get(&Integer::from(1_858_741)), Some(&1));
        assert_eq!(f.get(&Integer::from(53_799_857)), Some(&1));
        assert_eq!(f.get(&Integer::from(100_000_000_000_031_u64)), Some(&1));
    }
}
