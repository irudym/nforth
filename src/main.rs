use nforth::forth::Forth;

fn main() {
    let mut forth = Forth::new();

    forth
        .compile_vector("PRINTLN", vec![".", "CR", "."])
        .unwrap();

    let program1 = r#"
        : R% 10 */ 5 + 10 / ;

        : doubled 6 1000
        21 1 DO CR
        ." YEAR " I 2 U.R
        2DUP R% + DUP ."   BALANCE " .
        DUP 2000 > IF CR CR ." MORE THAN DOUBLED IN "
        I . ." YEARS " LEAVE THEN
        LOOP 2DROP ;

        doubled
        CR
    "#;

    forth.compile(program1).unwrap();

    forth.debug_show_words();

    forth.run().unwrap();
}
