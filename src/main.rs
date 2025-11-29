use nforth::forth::Forth;

fn main() {
    let mut forth = Forth::new();

    forth
        .compile_vector("PRINTLN", vec![".", "CR", "."])
        .unwrap();

    let program1 = r#"
        : ? @ . ;
        0 EGGS !
        " eggs I have!" EGGS +!
        EGGS ?
        CR

    "#;

    // TODO: .DATE name of the function raised an error!

    forth.compile(program1).unwrap();

    forth.debug_show_words();

    forth.run().unwrap();
}
