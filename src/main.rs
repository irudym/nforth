use nforth::forth::Forth;

fn main() {
    let mut forth = Forth::new();

    forth
        .compile_vector("PRINTLN", vec![".", "CR", "."])
        .unwrap();

    let program1 = r#"
        5 BEGIN 1 - DUP DUP . 0 > WHILE ." WORKING!" CR REPEAT
    "#;

    forth.compile(program1).unwrap();

    forth.debug_show_words();

    forth.run().unwrap();
}
