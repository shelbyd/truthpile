use std::{path::PathBuf, str::FromStr};
use structopt::*;

mod verify;

#[derive(Debug, StructOpt)]
struct Options {
    #[structopt(subcommand)]
    command: Command,
}

#[derive(Debug, StructOpt)]
enum Command {
    Verify(VerifyOpts),
}

#[derive(Debug, StructOpt)]
struct VerifyOpts {
    file: PathBuf,
}

fn main() -> anyhow::Result<()> {
    let opts = Options::from_args();

    match opts.command {
        Command::Verify(verify_opts) => {
            let contents = std::fs::read_to_string(&verify_opts.file)?;
            let ast: Ast = contents.parse()?;
            verify::verify(ast)
        }
    }
}

pub enum Ast {}

impl FromStr for Ast {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        todo!()
    }
}
