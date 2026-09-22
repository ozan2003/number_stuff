//! CLI to list all primes up to a bound using the sieve of Atkin.
use std::env::args;
use std::process::exit;
use std::time::Instant;

use number_stuff::utils::sieve::Primes;

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

    let Ok(n) = input.parse()
    else
    {
        eprintln!("Invalid input: {input}");
        exit(1);
    };

    let t0 = Instant::now();
    let primes = Primes::new(n);
    let elapsed = t0.elapsed();

    println!("Primes up to {n}:");
    for prime in &primes
    {
        println!("{prime}");
    }

    println!("Time taken: {:.6}s", elapsed.as_secs_f64());
}
