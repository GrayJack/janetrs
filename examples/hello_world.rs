use janetrs::{
    Janet, JanetArgs,
    client::{Error, JanetClient},
    env::CFunOptions,
};

#[janetrs::janet_fn(arity(fix(1)))]
fn testing(args: &mut [Janet]) -> Janet {
    use janetrs::JanetType::*;

    let arg = args.get_matches(0, &[Abstract, Buffer]);

    dbg!(arg);

    Janet::nil()
}

fn main() -> Result<(), Error> {
    let mut client = JanetClient::init_with_default_env()?;

    client.run("(print `Hello from Janet!`)")?;

    client.add_c_fn(CFunOptions::new(c"testing", testing));

    // let out = client.run("(+ 2 2)")?;

    let out = client.run("(testing nil)")?;

    println!("{out}");

    Ok(())
}
