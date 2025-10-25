use std::env::args;
use std::process::exit;
use std::time::Instant;

use number_stuff::utils::factors::totient;

fn main()
{
    let args: Vec<String> = args().collect();
    if args.len() < 2
    {
        eprintln!("Usage: {} <number>", args[0]);
        exit(1);
    }

    let num: i64 = args[1]
        .parse()
        .expect("Couldn't parse number.");

    let t0 = Instant::now();
    let totient = totient(num);
    let elapsed = t0.elapsed();

    println!("f({num}) = {totient}");
    println!("Took: {elapsed:?}");
}
