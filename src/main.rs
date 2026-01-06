use nforth::forth::Forth;
use std::fs;

fn main() {
    let mut forth = Forth::new();

    forth.compile_vector("PRINTLN", vec![".", "CR"]).unwrap();

    let _program1 = r#"
        : recursive DUP 0 > IF DUP . CR 1 - recursive  THEN ;
        10000000 recursive
    "#;

    // TODO: .DATE name of the function raised an error!
    //
    let program = fs::read_to_string("examples/recursion.forth")
        .expect("Should have been able to read the file");

    forth.compile(&program).unwrap();

    forth.debug_show_words();

    forth.run().unwrap();
}
