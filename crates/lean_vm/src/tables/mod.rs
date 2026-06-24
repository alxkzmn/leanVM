mod extension_op;
pub use extension_op::*;

mod blake3;
pub use blake3::*;

mod poseidon;
pub use poseidon::*;

mod table_enum;
pub use table_enum::*;

mod table_trait;
pub use table_trait::*;

mod execution;
pub use execution::*;

mod utils;
pub(crate) use utils::*;

// In logup interractions, the `domainsep` is the last entry of every tuple going into
// the bus. It separates the precompile tables from each other and from the memory and
// bytecode lookups, whose reserved domainseps are respectively 1 and 2.
//
//   Poseidon16  (odd >= 3): 3 + 2·flag_permute + 4·flag_out8 + 8·flag_left + 16·flag_left·offset_left
//   ExtensionOp (0 mod 4):  4·flag_be + 8·flag_add + 16·flag_dot_product + 32·flag_eq + 64·len
//   Blake3      (2 mod 4):  6
//
