#![feature(never_type)]

use std::path::PathBuf;
use structopt::*;

mod ast;
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
    file: String,
}

fn main() -> anyhow::Result<()> {
    let opts = Options::from_args();

    match opts.command {
        Command::Verify(verify_opts) => {
            let processed = preprocess(&format!("$[ {} $]", verify_opts.file))?;
            let ast = ast::parse(&processed)?;
            verify::verify(ast)
        }
    }
}

fn preprocess(s: &str) -> anyhow::Result<String> {
    let s = strip_comments(s)?;
    let mut s = s.as_str();

    let mut result = String::new();

    while let Some((pre, post)) = s.split_once("$[ ") {
        result += pre;
        let (file, post) = post
            .split_once(" $]")
            .ok_or(anyhow::anyhow!("Opening import without closing import"))?;

        result += &preprocess(std::fs::read_to_string(file)?.as_str())?;

        s = post;
    }

    result += s;
    Ok(result)
}

fn strip_comments(mut s: &str) -> anyhow::Result<String> {
    let mut result = String::new();

    while let Some((pre, post)) = s.split_once("$(") {
        result += pre;
        s = post
            .split_once("$)")
            .ok_or(anyhow::anyhow!("Opening comment without closing comment"))?
            .1;
    }

    result += s;
    Ok(result)
}
