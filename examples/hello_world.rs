use janetrs::client::{Error, JanetClient};

fn main() -> Result<(), Error> {
    let client = JanetClient::init_with_default_env()?;

    client.run("(print `Hello from Janet!`)")?;

    let out = client.run("(+ 2 2)")?;

    println!("{}", out);

    Ok(())
}
