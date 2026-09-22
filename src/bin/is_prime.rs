//! CLI to check primality of a number using Miller-Rabin.
use std::env::args;
use std::process::exit;
use std::time::Instant;

use malachite::Integer;
use number_stuff::utils::primes::is_prime;

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

    let num: Integer = input
        .parse()
        .expect("Couldn't parse number.");

    let t0 = Instant::now();
    let is_prime = is_prime(&num);
    let elapsed = t0.elapsed();

    if is_prime
    {
        println!("{num} is prime");
    }
    else
    {
        println!("{num} is not prime");
    }

    println!("Took: {:.6}s", elapsed.as_secs_f64());
}
