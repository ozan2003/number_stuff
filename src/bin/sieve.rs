use number_stuff::utils::primes::Primes;
use std::env::args;
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

    let Ok(n) = args[1].parse()
    else
    {
        eprintln!("Invalid input: {}", args[1]);
        exit(1);
    };

    let t0 = Instant::now();
    let primes = Primes::new(n);
    let elapsed = t0.elapsed();

    println!("Primes up to {n}:");
    for p in &primes
    {
        println!("{p}");
    }

    println!("Time taken: {elapsed:?}");
}
