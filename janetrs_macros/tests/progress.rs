#[test]
fn tests() {
    let t = trybuild::TestCases::new();
    t.pass("tests/00-test");
    t.compile_fail("tests/01-paths");
    t.compile_fail("tests/02-not-function");
    t.compile_fail("tests/03-not-mut");
    t.compile_fail("tests/04-not-ref");
    t.compile_fail("tests/05-wrong-args");
    t.compile_fail("tests/06-not-slice");
    t.pass("tests/07-mod");
    t.compile_fail("tests/08-wrong-args");
    t.compile_fail("tests/09-version-wrong");
    t.pass("tests/10-declare-janet-module");
    t.compile_fail("tests/11-declare_mod_errors");
}
