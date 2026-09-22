//! CLI to factorize a number, choosing trial division or Pollard's rho
//! based on input size.
use std::collections::BTreeMap;
use std::env::args;
use std::ops::Mul;
use std::process::exit;
use std::time::Instant;

use malachite::Integer;
use number_stuff::utils::factors::{pollards_rho, trial_division};

fn main()
{
    let args: Vec<String> = args().collect();
    let Some(input) = args.get(1)
    else
    {
        let program = args
            .first()
            .map_or("program", String::as_str);
        eprintln!("Usage: {program} <number>");
        exit(1);
    };

    if input.len() <= 12
    {
        let num: i64 = input
            .parse()
            .expect("Couldn't parse number.");

        println!("Using trial division:");
        time_and_print(&num, |n: &i64| trial_division(*n));
    }
    else
    {
        let num: Integer = input
            .parse()
            .expect("Couldn't parse number.");

        println!("Using Pollard's rho:");
        time_and_print(&num, pollards_rho);
    }
}

/// Helper function to avoid code duplication.
fn time_and_print<T, F>(num: &T, factor_func: F)
where
    T: Mul<T> + std::fmt::Display,
    <T as Mul<T>>::Output: Into<T>,
    F: FnOnce(&T) -> BTreeMap<T, u32>,
{
    let t0 = Instant::now();
    let factors = factor_func(num);
    let elapsed = t0.elapsed();

    print!("Factors of {num} =");
    for (factor, exponent) in &factors
    {
        print!(" {factor}^{exponent}");
    }
    println!();
    println!("Took: {:.6}s", elapsed.as_secs_f64());
}
