use nforth::forth::Forth;
use std::fs;

fn main() {
    let mut forth = Forth::new();

    forth.compile_vector("PRINTLN", vec![".", "CR"]).unwrap();

    let program1 = r#"
        : recursive 0 > IF 1 - recursive DUP . CR THEN ;
        10 recursive
    "#;

    // TODO: .DATE name of the function raised an error!
    //
    let _program = fs::read_to_string("examples/arrays.forth")
        .expect("Should have been able to read the file");

    forth.compile(&program1).unwrap();

    forth.debug_show_words();

    forth.run().unwrap();
}
