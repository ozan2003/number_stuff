use bit_vec::BitVec;
use rand::Rng;
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

#[cfg(test)]
mod tests
{
    use super::*;

    #[test]
    fn test_determine_k()
    {
        assert_eq!(determine_k(&Integer::parse("100").unwrap().complete()), 5); // < 10^3
        assert_eq!(determine_k(&Integer::parse("999").unwrap().complete()), 5);
        assert_eq!(determine_k(&Integer::parse("1000").unwrap().complete()), 10); // < 10^6
        assert_eq!(
            determine_k(&Integer::parse("999999").unwrap().complete()),
            10
        );
        assert_eq!(
            determine_k(&Integer::parse("1000000").unwrap().complete()),
            20
        ); // < 10^9
        assert_eq!(
            determine_k(
                &Integer::parse("999999999")
                    .unwrap()
                    .complete()
            ),
            20
        );
        assert_eq!(
            determine_k(
                &Integer::parse("1000000000")
                    .unwrap()
                    .complete()
            ),
            50
        ); // >= 10^9
        assert_eq!(
            determine_k(
                &Integer::parse("999999999999")
                    .unwrap()
                    .complete()
            ),
            50
        );
        assert_eq!(
            determine_k(
                &Integer::parse("1000000000000")
                    .unwrap()
                    .complete()
            ),
            50
        );
    }
}