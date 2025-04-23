use number_stuff::utils::primes::Primes;
use std::env::args;
use std::process::exit;

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

    let primes = Primes::new(n);

    println!("Primes up to {n}:");
    for p in &primes
    {
        println!("{p}");
    }
}
