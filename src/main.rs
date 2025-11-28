use nforth::forth::Forth;

fn main() {
    let mut forth = Forth::new();

    forth
        .compile_vector("PRINTLN", vec![".", "CR", "."])
        .unwrap();

    let program1 = r#"
        : HELLO ."Hello!" ;
        HELLO
        CR
        12 DATE !
        ."The current date is: "
        DATE @ .
        CR
        22 DATE !
        ."Now the date is: "
        DATE @ .
        CR
        "New Year" DATE !
        ."Now the date is string! "
        DATE @ .
        CR
    "#;

    forth.compile(program1).unwrap();

    forth.debug_show_words();

    forth.run().unwrap();
}
