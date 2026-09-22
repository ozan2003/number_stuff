//! CLI to compute Euler's totient function of a number.
use std::env::args;
use std::process::exit;
use std::time::Instant;

use number_stuff::utils::factors::totient;

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

    let num: i64 = input
        .parse()
        .expect("Couldn't parse number.");

    let t0 = Instant::now();
    let totient = totient(num);
    let elapsed = t0.elapsed();

    println!("f({num}) = {totient}");
    println!("Took: {:.6}s", elapsed.as_secs_f64());
}
