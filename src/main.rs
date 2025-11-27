use nforth::forth::Forth;

fn main() {
    let mut forth = Forth::new();

    forth
        .compile_vector("PRINTLN", vec![".", "CR", "."])
        .unwrap();

    let program1 = r#"

    "#;

    forth.compile(program1).unwrap();

    forth.debug_show_words();

    forth.run().unwrap();
}
