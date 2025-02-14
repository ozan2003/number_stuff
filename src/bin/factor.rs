use number_stuff::utils::factors::{pollards_rho, trial_division};
use rug::Integer;
use std::collections::BTreeMap;
use std::env::args;
use std::ops::Mul;
use std::process::exit;
use std::time::Instant;

fn main()
{
    let args: Vec<String> = args().collect();
    if args.len() < 2
    {
        eprintln!("Usage: {} <number>", args[0]);
        exit(1);
    }

    let input = &args[1];

    if input.len() <= 12
    {
        let num: i64 = input
            .parse()
            .expect("Couldn't parse number.");

        time_and_print(num, |n: &i64| trial_division(*n));
    }
    else
    {
        let num: Integer = input
            .parse()
            .expect("Couldn't parse number.");
        
        time_and_print(num, pollards_rho);
    }
}

/// Helper function to avoid code duplication.
fn time_and_print<T, F>(num: T, factor_func: F)
where
    T: Mul<T> + std::fmt::Debug,
    <T as Mul<T>>::Output: Into<T>,
    F: FnOnce(&T) -> BTreeMap<T, u32>,
{
    let t0 = Instant::now();
    let factors = factor_func(&num);
    let elapsed = t0.elapsed();

    println!("Factors of {:?}: {:?}", num, factors);
    println!("Took: {:?}", elapsed);
}
