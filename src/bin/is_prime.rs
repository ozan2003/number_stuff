use std::env::args;
use std::process::exit;
use std::time::Instant;

use number_stuff::utils::primes::is_prime;
use rug::Integer;

fn main()
{
    let args: Vec<String> = args().collect();
    if args.len() < 2
    {
        eprintln!("Usage: {} <number>", args[0]);
        exit(1);
    }

    let num: Integer = args[1]
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

    println!("Took: {elapsed:?}");
}
