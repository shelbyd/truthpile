use logos::*;
use nom::{
    branch::*,
    combinator::*,
    error::{Error, ErrorKind},
    multi::*,
    sequence::*,
    *,
};

#[derive(Debug, PartialEq, Eq)]
pub enum Stmt {
    ConstantDecl(Vec<String>),
    VarDecl(Vec<String>),
    Disjoint(Vec<String>),

    Func(Func),
    Expr(Expr),
    Assertion(Expr),
    Proof(Proof),

    Block(Vec<Stmt>),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Func {
    name: String,
    type_code: String,
    var: String,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Expr {
    name: String,
    type_code: String,
    symbols: Vec<String>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Proof {
    name: String,
    type_code: String,
    symbols: Vec<String>,
    labels: Vec<String>,
}

pub fn parse(s: &str) -> anyhow::Result<Vec<Stmt>> {
    let tokens = Token::lexer(s)
        .spanned()
        .map(|(token, span)| {
            if token == Token::Error {
                let end = core::cmp::min(s.len(), span.start + 40);
                Err(anyhow::anyhow!("unexpected token: {}", &s[span.start..end]))
            } else {
                Ok(token)
            }
        })
        .collect::<anyhow::Result<Vec<_>>>()?;

    let (_, stmts) =
        limit_err_len(10, root)(&tokens).map_err(|e| anyhow::anyhow!(e.to_string()))?;
    Ok(stmts)
}

type Toks<'t> = &'t [Token<'t>];

fn root(t: Toks) -> IResult<Toks, Vec<Stmt>> {
    let (t, stmts) = stmts(t)?;

    let (t, _) = eof(t).map_err(|e: Err<Error<Toks>>| match e {
        Err::Error(e) => {
            let end = core::cmp::min(e.input.len(), 10);
            Err::Error(Error::new(&e.input[..end], e.code))
        }
        _ => e,
    })?;

    Ok((t, stmts))
}

fn stmts(t: Toks) -> IResult<Toks, Vec<Stmt>> {
    many0(alt((
        //
        block,
        constant_decl,
        var_decl,
        func,
        expr,
        assertion,
        proof,
        disjoint,
    )))(t)
}

fn block(t: Toks) -> IResult<Toks, Stmt> {
    let (t, _) = tok(Token::BlockBegin)(t)?;
    let (t, s) = succeeds(terminated(stmts, tok(Token::BlockEnd)))(t)?;

    Ok((t, Stmt::Block(s)))
}

fn constant_decl(t: Toks) -> IResult<Toks, Stmt> {
    let (t, _) = tok(Token::C)(t)?;
    let (t, syms) = many1(math_sym)(t)?;
    let (t, _) = tok(Token::Term)(t)?;

    Ok((
        t,
        Stmt::ConstantDecl(syms.into_iter().map(|s| s.to_string()).collect()),
    ))
}

fn var_decl(t: Toks) -> IResult<Toks, Stmt> {
    let (t, _) = tok(Token::V)(t)?;
    let (t, syms) = many1(math_sym)(t)?;
    let (t, _) = tok(Token::Term)(t)?;

    Ok((t, Stmt::VarDecl(owned_vec(syms))))
}

fn func(t: Toks) -> IResult<Toks, Stmt> {
    let (t, name) = label(t)?;
    let (t, _) = tok(Token::F)(t)?;
    let (t, type_code) = math_sym(t)?;
    let (t, var) = math_sym(t)?;
    let (t, _) = tok(Token::Term)(t)?;

    Ok((
        t,
        Stmt::Func(Func {
            name: name.to_string(),
            type_code: type_code.to_string(),
            var: var.to_string(),
        }),
    ))
}

fn expr(t: Toks) -> IResult<Toks, Stmt> {
    let (t, name) = label(t)?;
    let (t, _) = tok(Token::E)(t)?;
    let (t, type_code) = math_sym(t)?;
    let (t, symbols) = many0(math_sym)(t)?;
    let (t, _) = tok(Token::Term)(t)?;

    Ok((
        t,
        Stmt::Expr(Expr {
            name: name.to_string(),
            type_code: type_code.to_string(),
            symbols: owned_vec(symbols),
        }),
    ))
}

fn assertion(t: Toks) -> IResult<Toks, Stmt> {
    let (t, name) = label(t)?;
    let (t, _) = tok(Token::A)(t)?;
    let (t, type_code) = math_sym(t)?;
    let (t, symbols) = many0(math_sym)(t)?;
    let (t, _) = tok(Token::Term)(t)?;

    Ok((
        t,
        Stmt::Assertion(Expr {
            name: name.to_string(),
            type_code: type_code.to_string(),
            symbols: owned_vec(symbols),
        }),
    ))
}

fn proof(t: Toks) -> IResult<Toks, Stmt> {
    let (t, name) = label(t)?;
    let (t, _) = tok(Token::P)(t)?;
    let (t, type_code) = math_sym(t)?;
    let (t, symbols) = many0(math_sym)(t)?;
    let (t, _) = tok(Token::Eq)(t)?;
    let (t, labels) = many0(math_sym)(t)?;
    let (t, _) = tok(Token::Term)(t)?;

    Ok((
        t,
        Stmt::Proof(Proof {
            name: name.to_string(),
            type_code: type_code.to_string(),
            symbols: owned_vec(symbols),
            labels: owned_vec(labels),
        }),
    ))
}

fn disjoint(t: Toks) -> IResult<Toks, Stmt> {
    let (t, _) = tok(Token::D)(t)?;
    let (t, symbols) = many_m_n(2, usize::MAX, math_sym)(t)?;
    let (t, _) = tok(Token::Term)(t)?;

    Ok((t, Stmt::Disjoint(owned_vec(symbols))))
}

fn owned_vec(s: Vec<&str>) -> Vec<String> {
    s.into_iter().map(|s| s.to_string()).collect()
}

fn tok(expected: Token) -> impl FnMut(Toks) -> IResult<Toks, ()> + '_ {
    move |t| match t.split_first() {
        Some((t, rest)) if t == &expected => Ok((rest, ())),

        None => Err(Err::Error(Error::new(t, ErrorKind::Eof))),
        Some(_) => Err(Err::Error(Error::new(t, ErrorKind::Tag))),
    }
}

fn math_sym<'t>(t: Toks<'t>) -> IResult<Toks<'t>, &'t str> {
    match t.split_first() {
        Some((Token::MathSymbol(s), rest)) => Ok((rest, s)),
        Some((Token::Label(s), rest)) => Ok((rest, s)),

        None => Err(Err::Error(Error::new(t, ErrorKind::Eof))),
        Some((_unexpected, _)) => Err(Err::Error(Error::new(t, ErrorKind::Tag))),
    }
}

fn label<'t>(t: Toks<'t>) -> IResult<Toks<'t>, &'t str> {
    match t.split_first() {
        Some((Token::Label(s), rest)) => Ok((rest, s)),

        None => Err(Err::Error(Error::new(t, ErrorKind::Eof))),
        Some((_unexpected, _)) => Err(Err::Error(Error::new(t, ErrorKind::Tag))),
    }
}

fn succeeds<'t, F, O>(mut inner: F) -> impl FnMut(Toks<'t>) -> IResult<Toks<'t>, O>
where
    F: FnMut(Toks<'t>) -> IResult<Toks<'t>, O>,
{
    move |t| {
        inner(t).map_err(|e| match e {
            Err::Error(e) => Err::Failure(e),
            _ => e,
        })
    }
}

fn limit_err_len<'t, F, O>(
    count: usize,
    mut inner: F,
) -> impl FnMut(Toks<'t>) -> IResult<Toks<'t>, O>
where
    F: FnMut(Toks<'t>) -> IResult<Toks<'t>, O>,
{
    move |t| {
        fn limit_len(count: usize, e: Error<Toks>) -> Error<Toks> {
            let len = core::cmp::min(e.input.len(), count);
            Error::new(&e.input[..len], e.code)
        }

        inner(t).map_err(|e| match e {
            Err::Error(e) => Err::Error(limit_len(count, e)),
            Err::Failure(e) => Err::Failure(limit_len(count, e)),
            _ => e,
        })
    }
}

#[derive(Logos, Debug, PartialEq)]
enum Token<'i> {
    #[token("$c")]
    C,

    #[token("$v")]
    V,

    #[token("$f")]
    F,

    #[token("$e")]
    E,

    #[token("$a")]
    A,

    #[token("$p")]
    P,

    #[token("$d")]
    D,

    #[token("$=")]
    Eq,

    #[token("${")]
    BlockBegin,
    #[token("$}")]
    BlockEnd,

    #[token("$.")]
    Term,

    #[regex(r"[a-zA-Z0-9-_\.]+", priority = 2)]
    Label(&'i str),

    #[regex(r"[^ \t\n\f\$]+", priority = 1)]
    MathSymbol(&'i str),

    #[error]
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Error,
}
