//! Prime number services.
//!
//! Provides functions to check if a number is prime and to perform primality
//! tests.
//!
//! # Functions
//!
//! * `is_prime` - Check if a number is prime using the Miller-Rabin primality
//!   test.
//! * `trial_division` - Check if a number is prime using trial division.
use malachite::base::num::arithmetic::traits::{ModPow as _, Parity as _};
use malachite::base::num::logic::traits::SignificantBits as _;
use malachite::{Integer, Natural};

use crate::utils::sieve::Primes;

/// Determine the number of iterations `k` based on the magnitude of `num`.
///
/// This function sets the number of iterations for the Miller-Rabin primality
/// test based on the bit length of the input number. Larger numbers require
/// more iterations to maintain the same probability of correctness.
///
/// # Arguments
///
/// * `num` - The number whose primality is being tested
///
/// # Returns
///
/// The number of iterations to use for the Miller-Rabin test.
///
/// # Details
///
/// For a k-iteration Miller-Rabin test, the probability of a composite number
/// being incorrectly identified as prime is at most 4^(-k).
fn determine_k(num: &Integer) -> u32
{
    // Use bit length to determine the number of rounds.
    let bits = num.significant_bits();

    if bits < 16
    {
        5 // Small numbers (< 2^16)
    }
    else if bits < 32
    {
        10 // Medium numbers (< 2^32)
    }
    else if bits < 64
    {
        20 // Large numbers (< 2^64)
    }
    else
    {
        50 // Very large numbers
    }
}

/// Check if a number is prime using the Miller-Rabin primality test.
/// Iteration number is determined heuristically based on the magnitude of
/// `num`.
///
/// # Arguments
///
/// * `num` - The number to check for primality.
///
/// # Returns
///
/// `true` if `num` is probably prime, `false` otherwise.
///
/// # Examples
///
/// ```
/// use malachite::Integer;
///
/// let num = Integer::from(18014398509488327u64);
/// assert!(is_prime(&num));
/// ```
///
/// # Panics
///
/// Panics if the `pow_mod` operation fails.
#[expect(
    clippy::many_single_char_names,
    reason = "single-char names mirror the standard Miller-Rabin notation"
)]
#[must_use]
pub fn is_prime(num: &Integer) -> bool
{
    /*
     * Fermat's Little Theorem:
     *  Let `p` a prime number and `a` is any integer that's not divisible by
     * `p`,  then:
     *
     *  a^(p-1) === 1 (mod p)
     *
     *
     * To test a number `n` for primality, we can pick a random number `a`
     * (called "witness") and check if the following holds:
     *
     * a^(n-1) === 1 (mod n)
     *
     * If the above doesn't hold, then `n` is composite since Fermat's Little
     * Theorem tells us this equation must hold for prime numbers.
     *
     * But, some composite numbers also satisfy the above equation. These are
     * called "Carmichael numbers" e.g 561.
     *
     * This is where the Miller-Rabin primality test comes in. Instead of
     * just checking if a^(n-1) === 1 (mod n), it delves deeper.
     *
     * When n is prime and n-1 = 2^s * d (d is odd), we can write:
     *
     * a^(n-1) = a^(2^s * d) = (a^d)^(2^s)
     *
     * If n is prime, this sequence:
     *
     * a^d, a^(2d), a^(4d), a^(8d), ... a^(2^s * d)
     *
     * must either:
     * - Start with 1
     * - Start with something else but contain -1 (or n-1) somewhere.
     *
     * If n is composite, at least 75% of bases a will reveal n is composite.
     * Thus, after k iterations, the probability of `n` being prime is 1/4^k.
     */
    // Early returns for small numbers and negatives.
    if *num < 2
    {
        return false;
    }
    if *num == 2 || *num == 3
    {
        return true;
    }

    if num.even()
    {
        return false;
    }

    // Determine k based on magnitude of n.
    let k = determine_k(num);

    // Work with the magnitude from here on; `num` is odd and at least 5.
    let n = Natural::try_from(num).expect("`num` is positive");
    let one = Natural::from(1u64);
    let two = Natural::from(2u64);
    let n_minus_one = &n - &one;

    // Step 1: Decompose n-1 into d * 2^s.
    let (s, d) = {
        let mut s: i32 = 0;
        let mut d = n_minus_one.clone();

        while d.even()
        {
            d >>= 1u64;
            s += 1;
        }
        (s, d)
    };

    // Step 2: Search for a witness.
    let mut rng = urandom::new();
    // Candidate bases live in [2, n - 2]; reduce random bits modulo n - 3.
    let span = &n_minus_one - &two;
    let words = num.significant_bits().div_ceil(64);
    // Step 3: Repeat k times.
    for _ in 0..k
    {
        // Randomly chosen base a, 2 <= a <= n-2
        let a: Natural = {
            // Generate enough random bits to cover the range, then reduce
            // modulo `span` to land in [2, n - 2].
            let mut raw = Natural::from(0u64);
            for _ in 0..words
            {
                raw <<= 64u64;
                raw += Natural::from(rng.next::<u64>());
            }
            raw % &span + &two
        };

        // Compute x = a^d % n.
        let mut x = (&a).mod_pow(&d, &n);

        if x == one || x == n_minus_one
        {
            // `num` passes the test for this `a`.
            continue;
        }

        // Otherwise, square `x` repeatedly up to `s-1` times.
        for _ in 0..s - 1
        {
            x = (&x).mod_pow(&two, &n);

            // Check is x === -1 (mod n).
            // x == n - 1 is equivalent to x == -1 (mod n).
            if x == n_minus_one
            {
                // If found, `num` passes the test for this `a`.
                break;
            }
        }

        // If never found, `num` is composite.
        if x != n_minus_one
        {
            return false;
        }
    }

    true
}

/// Check if a number is prime using trial division.
///
/// This function uses a prime sieve to efficiently test divisibility of `num`
/// by all primes up to the square root of `num`.
///
/// # Arguments
///
/// * `num` - The number to check for primality.
///
/// # Returns
///
/// `true` if `num` is prime, `false` otherwise.
///
/// # Performance
///
/// This method is efficient for numbers up to approximately 10^12. For larger
/// numbers, consider using the probabilistic `is_prime()` function instead.
///
/// # Examples
///
/// ```
/// use number_stuff::utils::primes::trial_division;
///
/// assert!(trial_division(18014398509482147));
/// assert!(!trial_division(18014398509482171));
/// assert!(trial_division(18014398509482329));
/// assert!(!trial_division(18014398509482357));
/// ```
///
/// # Panics
///
/// The function may panic when initializing the sieve or if the square root of
/// `num` cannot be represented as a `usize`.
#[must_use]
pub fn trial_division(num: u64) -> bool
{
    if num < 2
    {
        return false;
    }

    if num.is_multiple_of(2)
    {
        return num == 2;
    }

    // Any number greater than 1 is divided by a prime number less than its
    // square root.
    for i in Primes::new(
        usize::try_from(num.isqrt()).expect("Failed to convert u64 to usize"),
    )
    .iter()
    .map(|x| x as u64)
    {
        if num.is_multiple_of(i)
        {
            return false;
        }
    }

    true
}

#[cfg(test)]
mod tests
{
    use std::sync::LazyLock;

    use super::*;

    // Primes up to 1000
    static SMALL_PRIMES: &[u32] = &[
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
        71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139,
        149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
        227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293,
        307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383,
        389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569,
        571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647,
        653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743,
        751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839,
        853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
        947, 953, 967, 971, 977, 983, 991, 997,
    ];

    // Large prime number for testing
    static BIG_PRIME: LazyLock<Integer> = LazyLock::new(|| {
        "800948954241637326367289644750448487839117926303848998020309\
        1882856589695259576866912252471851775792381635152371769187095490468400064936928273574383567528 \
        121072690778050973811430761398678258395995371555894454671120879811384840595312486689823936748878302 \
        83487720338800489565021330252166958070609444129096599915927491089204574668996261366285398022946178 \
        5588155810915576292016665079696314903061261426009609240670414640717372982383625995755248125698223 \
        1856327486667940207811726091388832774553459734155793"
            .split_whitespace()
            .collect::<String>()
            .parse()
            .expect("Couldn't parse big prime")
    });

    #[test]
    fn test_determine_k()
    {
        let test_cases = [
            ("100", 5),
            ("999", 5),
            ("1000", 10),
            ("999999", 10),
            ("1000000", 20),
            ("999999999", 20),
            ("1000000000", 50),
            ("999999999999", 50),
            ("1000000000000", 50),
        ];

        for (num_str, expected) in test_cases
        {
            assert_eq!(
                determine_k(
                    &num_str
                        .parse::<Integer>()
                        .expect("Couldn't parse test number")
                ),
                expected
            );
        }
    }

    #[test]
    fn test_is_prime()
    {
        // Test small primes
        assert!(
            SMALL_PRIMES
                .iter()
                .map(|&x| Integer::from(x))
                .all(|x| is_prime(&x))
        );

        // Test big prime
        assert!(is_prime(&BIG_PRIME));
    }

    #[test]
    fn test_trial_division()
    {
        assert!(
            SMALL_PRIMES
                .iter()
                .take(100)
                .copied()
                .all(|x| trial_division(u64::from(x)))
        );
    }
}
