use janetrs::client::{Error, JanetClient};

fn main() -> Result<(), Error> {
    let client = JanetClient::init()?.with_default_env();

    client.run("(print `Hello from Janet!`)")?;

    Ok(())
}
