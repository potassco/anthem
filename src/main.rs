pub mod analyzing;
pub mod breaking;
pub mod command_line;
pub mod convenience;
pub mod formatting;
pub mod normalizing;
pub mod parsing;
pub mod simplifying;
pub mod syntax_tree;
pub mod translating;
pub mod verifying;

use anyhow::Result;

fn main() -> Result<()> {
    crate::command_line::procedures::main()
}
