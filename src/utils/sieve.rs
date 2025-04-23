//! Prime number sieve.
//!
//! Provides a separated prime number sieve implementation.
//!
//! # Structs
//!
//! * `Primes` - A prime sieve.
//! * `PrimesIterator` - An iterator over prime numbers in a Primes sieve.
use bit_vec::BitVec;

/// A prime sieve.
pub struct Primes
{
    primes: BitVec,
}

/// An iterator over prime numbers in a Primes sieve
///
/// # Examples
///
/// ```
/// use crate::utils::sieve::Primes;
///
/// let primes = Primes::new(100);
///
/// // Iterate through all primes up to 100
/// for prime in primes.iter() {
///     println!("{}", prime);
/// }
///
/// // Use iterator combinators
/// let first_five_primes: Vec<_> = primes.iter().take(5).collect();
/// assert_eq!(first_five_primes, vec![2, 3, 5, 7, 11]);
/// ```
pub struct PrimesIterator<'a>
{
    primes: &'a BitVec,
    current_index: usize,
}

impl Primes
{
    /// Return all primes <= n using the sieve of Atkin.
    ///
    /// # Arguments
    ///
    /// * `n` - The upper bound up to which to find all primes
    ///
    /// # Returns
    ///
    /// A `Primes` struct containing a sieve with all primes up to `n`
    ///
    /// # Examples
    ///
    /// ```
    /// use number_stuff::utils::sieve::Primes;
    ///
    /// let primes = Primes::new(100);
    /// assert!(primes.is_prime(2));
    /// assert!(primes.is_prime(3));
    /// assert!(primes.is_prime(5));
    /// assert!(primes.is_prime(97));
    /// assert!(!primes.is_prime(4));
    /// assert!(!primes.is_prime(100));
    /// ```
    #[must_use]
    pub fn new(n: usize) -> Self
    {
        /*
         * The Sieve of Atkin works by identifying prime numbers based on
         * quadratic forms and their remainders when divided by 60.
         *
         * Primes greater than 3 can be expressed as 6k +/- 1.
         * This means primes are congruent to:
         *
         * 1, 5, 7, 11, 13, 17, 19, 23, 29, 31, ... (mod 60)
         *
         * Three quadratic forms are used to generate prime candidates:
         *
         * 1) 4x^2 + y^2: Produces candidates with remainders 1, 13, 17, 29, 37, 41,
         *    49, 53 (mod 60)
         * 2) 3x^2 + y^2: Produces candidates with remainders 7, 19, 31, 43 (mod 60)
         * 3) 3x^2 - y^2: Produces candidates with remainders 11, 23, 47, 59 (mod 60)
         *
         * By working modulo 60, we can efficiently identify which numbers are prime
         * candidates.
         */
        let mut primes = BitVec::from_elem(n + 1, false);

        if n < 2
        {
            return Primes { primes };
        }

        // Set 2, 3, and 5 as prime manually.
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
        primes.set(5, true);

        let sqrt_n = n.isqrt() + 1;

        // Step 1: Mark potential primes based on the quadratic forms
        for x in 1..sqrt_n
        {
            for y in 1..sqrt_n
            {
                // First quadratic form: 4x^2 + y^2
                let n1 = 4 * x * x + y * y;
                if n1 <= n
                {
                    let r = n1 % 60;
                    if r == 1 ||
                        r == 13 ||
                        r == 17 ||
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
                    let r = n2 % 60;
                    if r == 7 || r == 19 || r == 31 || r == 43
                    {
                        primes.set(n2, !primes[n2]);
                    }
                }

                // Third quadratic form: 3x^2 - y^2 (x > y)
                if x > y
                {
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

        // Step 2: Remove composite numbers by sieving
        for i in 5..=sqrt_n
        {
            // If i is marked as a prime candidate
            if primes[i]
            {
                // Mark all multiples of i as composite
                // Start from i*i since smaller multiples would have been marked already
                let mut multiple = i * i;
                while multiple <= n
                {
                    primes.set(multiple, false);
                    multiple += i; // Mark each multiple of i
                }
            }
        }

        Primes { primes }
    }

    /// Check if a number is prime.
    ///
    /// # Arguments
    ///
    /// * `num` - The number to check for primality
    ///
    /// # Returns
    ///
    /// Returns `true` if the number is prime, `false` otherwise.
    /// If `num` is larger than the sieve's maximum value, returns `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use number_stuff::utils::sieve::Primes;
    ///
    /// let primes = Primes::new(100);
    /// assert!(primes.is_prime(7));
    /// assert!(!primes.is_prime(6));
    /// // Larger than sieve range
    /// assert!(!primes.is_prime(101));
    /// ```
    #[must_use]
    pub fn is_prime(&self, num: usize) -> bool
    {
        self.primes.get(num).unwrap_or(false)
    }

    /// Return the nth prime number, 0-indexed.
    ///
    /// # Arguments
    ///
    /// * `n` - The index of the prime to retrieve (0-indexed)
    ///
    /// # Returns
    ///
    /// Returns the nth prime number as `Some(prime)` or `None` if the index
    /// is out of bounds for the sieve.
    ///
    /// # Examples
    ///
    /// ```
    /// use number_stuff::utils::sieve::Primes;
    ///
    /// let primes = Primes::new(100);
    /// assert_eq!(primes.nth(0), Some(2));  // 0th prime is 2
    /// assert_eq!(primes.nth(1), Some(3));  // 1st prime is 3
    /// assert_eq!(primes.nth(4), Some(11)); // 4th prime is 11
    /// // The 26th prime is 101, which is larger than the sieve's maximum
    /// assert_eq!(primes.nth(25), None);
    /// ```
    #[must_use]
    pub fn nth(&self, n: usize) -> Option<usize>
    {
        self.iter().nth(n)
    }

    /// Returns an iterator over all prime numbers in the sieve
    ///
    /// # Returns
    ///
    /// A `PrimesIterator` that yields all prime numbers from the sieve in
    /// ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use number_stuff::utils::sieve::Primes;
    ///
    /// let primes = Primes::new(20);
    /// let primes_vec: Vec<_> = primes.iter().collect();
    /// assert_eq!(primes_vec, vec![2, 3, 5, 7, 11, 13, 17, 19]);
    /// ```
    #[must_use]
    pub fn iter(&self) -> PrimesIterator
    {
        PrimesIterator {
            primes: &self.primes,
            current_index: 0,
        }
    }
}

impl Iterator for PrimesIterator<'_>
{
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item>
    {
        while self.current_index < self.primes.len()
        {
            let index = self.current_index;
            self.current_index += 1;

            if self.primes.get(index).unwrap_or(false)
            {
                return Some(index);
            }
        }
        None
    }
}

impl<'a> IntoIterator for &'a Primes
{
    type Item = usize;
    type IntoIter = PrimesIterator<'a>;

    fn into_iter(self) -> Self::IntoIter
    {
        self.iter()
    }
}

#[cfg(test)]
mod tests
{
    use super::*;

    // Primes up to 1000
    static SMALL_PRIMES: &[u32] = &[
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
        97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
        283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
        509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
        631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743,
        751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
        877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997,
    ];

    #[test]
    fn test_primes()
    {
        let primes = Primes::new(5000);
        assert_eq!(
            primes
                .iter()
                .take(SMALL_PRIMES.len())
                .collect::<Vec<_>>(),
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
    fn test_iterator_implementation()
    {
        let primes = Primes::new(100);

        // Test direct iteration
        let collected: Vec<_> = primes.iter().collect();
        let expected: Vec<_> = vec![
            2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
            89, 97,
        ];
        assert_eq!(collected, expected);

        // Test IntoIterator implementation
        let for_loop_collected: Vec<_> = (&primes).into_iter().collect();
        assert_eq!(for_loop_collected, expected);

        // Test standard iterator combinators
        let first_five: Vec<_> = primes.iter().take(5).collect();
        assert_eq!(first_five, vec![2, 3, 5, 7, 11]);

        // Test skip and take
        let middle_five: Vec<_> = primes.iter().skip(5).take(5).collect();
        assert_eq!(middle_five, vec![13, 17, 19, 23, 29]);

        // Test filter
        let mod_3_is_1: Vec<_> = primes
            .iter()
            .filter(|&p| p % 3 == 1)
            .take(5)
            .collect();
        assert_eq!(mod_3_is_1, vec![7, 13, 19, 31, 37]);
    }
}
