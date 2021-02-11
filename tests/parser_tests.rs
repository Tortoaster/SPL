use std::fs;

use spl::parser::Result;
use spl::parser::SPL;

const RES_DIR: &str = "tests/res/";

#[test]
fn tests() -> Result<()> {
    let code = fs::read_to_string(RES_DIR.to_owned() + "fac.spl").expect("File inaccessible");
    SPL::new(code.as_str())?;
    Ok(())
}
