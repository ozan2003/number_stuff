use bit_vec::BitVec;
use rug::rand::RandState;
use rug::{Complete, Integer};

/// Determine the number of iterations `k` based on the magnitude of `num`.
fn determine_k(num: &Integer) -> u32
{
    if *num < Integer::i_pow_u(10, 3).complete()
    {
        5
    }
    else if *num < Integer::i_pow_u(10, 6).complete()
    {
        10
    }
    else if *num < Integer::i_pow_u(10, 9).complete()
    {
        20
    }
    else
    {
        50
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
/// `true` if `num` is prime, `false` otherwise.
///
/// # Examples
///
/// ```
/// use rug::Integer;
///
/// let num = Integer::from(18014398509488327);
/// assert!(is_prime(&num));
/// ```
///
/// # Panics
///
/// Panics if the `pow_mod` operation fails.
#[allow(clippy::many_single_char_names)]
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
    // Early returns for small numbers
    match num.to_i32()
    {
        | Some(n) if n <= 1 => return false,
        | Some(n) if n <= 3 => return true,
        | _ =>
        {}
    }

    if num.is_even()
    {
        return false;
    }

    // Determine k based on magnitude of n.
    let k = self::determine_k(num);

    // Step 1: Decompose n-1 into d * 2^s.
    let (s, d) = {
        let mut s: i32 = 0;
        let mut d: Integer = (num - Integer::ONE).complete();

        while d.is_even()
        {
            d >>= 1;
            s += 1;
        }
        (s, d)
    };

    // Step 2: Search for a witness.
    let mut rng = RandState::new();
    // Step 3: Repeat k times.
    for _ in 0..k
    {
        // Randomly chosen base a, 2 <= a <= n-2 -> 0 <= a - 2 <= n-4
        let a: Integer = (num - Integer::from(4)).random_below(&mut rng) + 2;

        // Compute x = a^d % n.
        let mut x = a
            .pow_mod_ref(&d, num)
            .expect("Couldn't complete pow_mod operation.")
            .complete();

        if x == *Integer::ONE || x == (num - Integer::ONE).complete()
        {
            // `num` passes the test for this `a`.
            continue;
        }

        // Otherwise, square `x` repeatedly up to `s-1` times.
        for _ in 0..s - 1
        {
            x.pow_mod_mut(&Integer::from(2), num)
                .unwrap();

            // Check is x === -1 (mod n).
            // x == num - 1 is equivalent to x == -1 (mod n).
            if x == (num - Integer::ONE).complete()
            {
                // If found, `num` passes the test for this `a`.
                break;
            }
        }

        // If never found, `num` is composite.
        if x != (num - Integer::ONE).complete()
        {
            return false;
        }
    }

    true
}

////////////////////////////////////////////////////////////////////////////////////////////
/// A prime sieve.
pub struct Primes
{
    primes: BitVec,
}

impl Primes
{
    /// Return all primes <= n using the sieve of Atkin.
    #[must_use]
    pub fn new(n: usize) -> Self
    {
        /*
         * Primes greater than 3 can be expressed as 6k +/- 1.
         * This means primes are congruent to:
         *
         * 1, 5, 7, 11, 13, 17, 19, 23, 29, 31, ... (mod 60)
         *
         * Three quadratic forms are used to generate primes:
         *
         * 1) 4x^2 + y^2: Covers primes 1, 5, 13, ... (mod 60)
         * 2) 3x^2 + y^2: Covers primes 7, 19, 31, ... (mod 60)
         * 3) 3x^2 - y^2: Covers primes 11, 23, 47, ... (mod 60)
         *
         * these forms produce numbers that are congruent to specific remainders
         * modulo 60.
         *
         * By working modulo 60, we can efficiently identify which numbers are prime
         * candidates.
         */
        let mut primes = BitVec::from_elem(n + 1, false);

        if n < 2
        {
            return Primes { primes };
        }

        // Set 2 and 3 as prime manually.
        if n >= 2
        {
            primes.set(2, true);
        }
        if n >= 3
        {
            primes.set(3, true);
        }

        if n < 5
        {
            return Primes { primes };
        }

        let sqrt_n = n.isqrt() + 1;

        // Iterate all pairs of integers (x, y) where 1 <= x, y <= sqrt(n).
        // For each pair, check their remainders modulo 60.
        for x in 1..sqrt_n
        {
            for y in 1..sqrt_n
            {
                // First quadratic form: 4x^2 + y^2
                let n1 = 4 * x * x + y * y;
                if n1 <= n
                {
                    // if n1 <= n and n1 % 60 E {1, 13, 17, 29, 37, 41, 49, 53}
                    // flip the n1.
                    let r = n1 % 60;
                    if r == 1 ||
                        r == 5 ||
                        r == 13 ||
                        r == 17 ||
                        r == 25 ||
                        r == 29 ||
                        r == 37 ||
                        r == 41 ||
                        r == 49 ||
                        r == 53
                    {
                        primes.set(n1, !primes[n1]);
                    }
                }

                // Second quadratic form: 3x^2 + y^2
                let n2 = 3 * x * x + y * y;
                if n2 <= n
                {
                    // if n2 <= n and n2 % 60 E {7, 19, 31, 43}
                    // flip the n2.
                    let r = n2 % 60;
                    if r == 7 || r == 19 || r == 31 || r == 43
                    {
                        primes.set(n2, !primes[n2]);
                    }
                }

                // Third quadratic form: 3x^2 - y^2 (x > y)
                if x > y
                {
                    // if n3 <= n and n3 % 60 E {11, 23, 47, 59}
                    // flip the n3.
                    let n3 = 3 * x * x - y * y;
                    if n3 <= n
                    {
                        let r = n3 % 60;
                        if r == 11 || r == 23 || r == 47 || r == 59
                        {
                            primes.set(n3, !primes[n3]);
                        }
                    }
                }
            }
        }

        // Eliminate composite numbers.
        for i in 5..=sqrt_n
        {
            // Mark all multiples of i^2 as composite.
            if primes[i]
            {
                let mut n_sq = i * i;
                while n_sq <= n
                {
                    primes.set(n_sq, false);
                    n_sq += i * i;
                }
            }
        }

        Primes { primes }
    }

    /// Check if a number is prime.
    #[must_use]
    pub fn is_prime(&self, num: usize) -> bool
    {
        self.primes.get(num).unwrap_or(false)
    }

    /// Return the nth prime number, 0-indexed.
    #[must_use]
    pub fn nth(&self, n: usize) -> Option<usize>
    {
        self.primes
            .iter()
            .enumerate()
            .filter(|&(_i, b)| b)
            .nth(n)
            .map(|(i, _b)| i)
    }

    pub fn iter(&self) -> impl Iterator<Item = usize>
    {
        self.primes
            .iter()
            .enumerate()
            .filter(|&(_i, b)| b)
            .map(|(i, _b)| i)
    }
}

/// Check if a number is prime using trial division.
///
/// # Arguments
///
/// * `num` - The number to check for primality.
///
/// # Returns
///
/// `true` if `num` is prime, `false` otherwise.
///
/// # Examples
///
/// ```
/// assert!(trial_division(18014398509482147));
/// assert!(!trial_division(18014398509482171));
/// assert!(trial_division(18014398509482329));
/// assert!(!trial_division(18014398509482357));
/// ```
///
/// # Panics
///
/// The function may panic when initializing the sieve.
#[must_use]
pub fn trial_division(num: u64) -> bool
{
    if num < 2
    {
        return false;
    }

    if num % 2 == 0
    {
        return num == 2;
    }

    // Any number greater than 1 is divided by a prime number less than its square
    // root.
    for i in Primes::new(usize::try_from(num.isqrt()).expect("Failed to convert u64 to usize"))
        .iter()
        .map(|x| x as u64)
    {
        if num % i == 0
        {
            return false;
        }
    }

    true
}

#[cfg(test)]
mod tests
{
    use super::*;
    use lazy_static::lazy_static;

    lazy_static! {
        // Primes up to 1000
        static ref SMALL_PRIMES: [u32; 168] = [
            2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
            89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
            181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271,
            277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379,
            383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479,
            487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599,
            601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
            709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823,
            827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
            947, 953, 967, 971, 977, 983, 991, 997
        ];

        // Large prime number for testing
        static ref BIG_PRIME: Integer = Integer::parse("800948954241637326367289644750448487839117926303848998020309 \
        1882856589695259576866912252471851775792381635152371769187095490468400064936928273574383567528 \
        121072690778050973811430761398678258395995371555894454671120879811384840595312486689823936748878302 \
        83487720338800489565021330252166958070609444129096599915927491089204574668996261366285398022946178 \
        5588155810915576292016665079696314903061261426009609240670414640717372982383625995755248125698223 \
        1856327486667940207811726091388832774553459734155793").unwrap().complete();
    }

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
                determine_k(&Integer::parse(num_str).unwrap().complete()),
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
    fn test_primes()
    {
        let primes = Primes::new(5000);
        assert_eq!(
            primes.iter().take(SMALL_PRIMES.len()).collect::<Vec<_>>(),
            SMALL_PRIMES
                .iter()
                .map(|&x| x as usize)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_nth()
    {
        let primes = Primes::new(1000);
        for (i, &prime) in SMALL_PRIMES.iter().enumerate()
        {
            assert_eq!(primes.nth(i), Some(prime as usize));
        }
    }

    #[test]
    fn test_trial_division()
    {
        assert!(
            SMALL_PRIMES
                .iter()
                .take(100)
                .copied()
                .all(|x| trial_division(x as u64))
        );
    }
}
