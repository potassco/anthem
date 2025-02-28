use clap::CommandFactory;
use clap_complete::{generate_to, Shell};
use std::{env, fs, io::Error, path::Path};

include!("src/command_line/arguments.rs");

fn main() -> Result<(), Error> {
    let mut cmd = Arguments::command();

    let out_dir = Path::new(&env::var_os("OUT_DIR").unwrap()).join("completions/");
    fs::create_dir_all(Path::new(&out_dir))?;

    for &shell in Shell::value_variants() {
        generate_to(shell, &mut cmd, "anthem", &out_dir)?;
    }

    println!("cargo:rerun-if-changed=src/command_line/arguments.rs");

    Ok(())
}
