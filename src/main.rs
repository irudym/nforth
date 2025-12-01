use nforth::forth::Forth;

fn main() {
    let mut forth = Forth::new();

    forth
        .compile_vector("PRINTLN", vec![".", "CR", "."])
        .unwrap();

    let program1 = r#"

        ARRAY1 ARRAY
        [1,2,3 ,4, 5] ARRAY1 !
        ( get the second element of the array)

        1 ARRAY1 @ . CR

        (get the forth element)
        3 ARRAY1 @ . CR

        (get the first and the fifth elements)
        [0, 4] ARRAY1 @ . ." " . CR

        (change array value at the index)
        67 [0] ARRAY1 [!]
        ."Array: " ARRAY1 [@] . CR

        [1,2 , 4.5, "Hello!" ] mixed_array !

        : new[+] [@] SWAP [@] + ;

        mixed_array [@] . CR
        mixed_array ARRAY1  new[+] new_array !
        ."New array: " new_array [@] . CR



    "#;

    // TODO: .DATE name of the function raised an error!

    forth.compile(program1).unwrap();

    forth.debug_show_words();

    forth.run().unwrap();
}
