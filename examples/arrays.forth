ARRAY1 ARRAY
        [1,2,3 ,4, 5] ARRAY1 !
        ( get the second element of the array)

        1 ARRAY1 @ . CR

        (get the forth element)
        3 ARRAY1 @ . CR

        (get the first and the fifth elements)
        [0, 4] ARRAY1 @ . ." " . CR

        (change array value at the index or indexes)
        67 [0, 3] ARRAY1 [!]
        ."Array: " ARRAY1 [@] . CR

        [1,2 , 4.5, "Hello!" ] mixed_array !

        : new[+] [@] SWAP [@] + ; ( there is a special command for that: [+])

        mixed_array [@] . CR
        mixed_array ARRAY1  new[+] new_array !
        ."New array: " new_array [@] PRINTLN
