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

        220 CONST LIMIT

        ."The speed limit is: " LIMIT .

        330 CONSTANT VOLTAGE

         15905 CONST SHUTTER

         : OPEN 1 SWAP ! ;
         : CLOSE 0 SWAP ! ;

         SHUTTER OPEN

    "#;

    // TODO: .DATE name of the function raised an error!

    forth.compile(program1).unwrap();

    forth.debug_show_words();

    forth.run().unwrap();
}
