//! Number theory utilities for competitive programming.
#![expect(
    clippy::arithmetic_side_effects,
    reason = "math code relies on operands staying in range for the supported \
              domains; wrapping is not a concern here"
)]
#![expect(
    clippy::min_ident_chars,
    reason = "mathematical notation conventionally uses single-character \
              identifiers (n, p, d, x, ...)"
)]

pub mod utils;
