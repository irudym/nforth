use crate::parser::{FunctionDefinition, parse};
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::{cmp, panic};

pub type Address = usize;
// type Cell = i32;

#[derive(Clone, Debug)]
pub enum Cell {
    INT(i32),
    FLOAT(f32),
    STRING(String),
    BOOL(bool),
}

impl Cell {
    fn type_name(&self) -> String {
        use Cell::*;
        match self {
            INT(_) => "INT".to_string(),
            FLOAT(_) => "FLOAT".to_string(),
            STRING(_) => "STRING".to_string(),
            BOOL(_) => "BOOL".to_string(),
        }
    }

    fn add(&self, value: &Cell) -> Result<Cell, String> {
        use Cell::*;
        match (self, value) {
            (INT(a), INT(b)) => Ok(INT(a + b)),
            (FLOAT(a), FLOAT(b)) => Ok(FLOAT(a + b)),
            (STRING(s1), STRING(s2)) => Ok(STRING(format!("{}{}", s1, s2))),
            (INT(a), FLOAT(b)) => Ok(FLOAT(*a as f32 + b)),
            (FLOAT(a), INT(b)) => Ok(FLOAT(a + *b as f32)),
            (STRING(s1), INT(b)) => Ok(STRING(format!("{}{}", s1, b))),
            (INT(a), STRING(s2)) => Ok(STRING(format!("{}{}", a, s2))),
            (STRING(s1), FLOAT(b)) => Ok(STRING(format!("{}{}", s1, b))),
            (FLOAT(a), STRING(s2)) => Ok(STRING(format!("{}{}", a, s2))),
            _ => Err("Error: cannot execute Cell::add, unsupported types".into()),
        }
    }
}

impl Display for Cell {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Cell::*;
        let result = match self {
            INT(val) => val.to_string(),
            FLOAT(val) => val.to_string(),
            STRING(val) => val.clone(),
            BOOL(val) => val.to_string(),
        };
        write!(f, "{}", result)?;
        Ok(())
    }
}

enum Word {
    Primitive(Box<dyn Fn(&mut Forth)>),
    Composite(Vec<Address>),
    Jump(i32),        // unconditional jump to the given offset
    JumpIfZero(i32),  // conditional jump by offset
    JumpLoop(i32),    // loop jump to do
    JumpLoopInc(i32), // incremental loop. value is teh offes to the command next to DO
    Push(Cell),       // push value to the data stack
    Var(Address),     // variable, address pointd to the value in Variable heap.
}

impl Display for Word {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Word::*;
        let result = match self {
            Primitive(_) => "PRIMITIVE".to_string(),
            Composite(vec) => format!("COMPOSITE({:?})", vec),
            Jump(offset) => format!("Jump({})", offset),
            JumpIfZero(offset) => format!("JumpIfZero({})", offset),
            JumpLoop(offset) => format!("JumpLoop({})", offset),
            JumpLoopInc(offset) => format!("JumpLoopInc({})", offset),
            Push(val) => format!("Push({})", val),
            Var(addr) => format!("Variable({})", addr),
        };
        write!(f, "{}", result)?;
        Ok(())
    }
}

pub struct Forth {
    data_stack: Vec<Cell>,
    return_stack: Vec<Cell>,
    dictionary: HashMap<String, Address>,
    words: Vec<Word>,
    variables: Vec<Cell>, // heap to store variable values
                          //ip: Address, // instruction pointer
}

fn fixed_right(s: &str, width: usize) -> String {
    let truncated = if s.len() > width {
        &s[s.len() - width..] // keep rightmost part
    } else {
        s
    };
    format!("{:>width$}", truncated, width = width)
}

impl Forth {
    pub fn new() -> Self {
        let mut forth = Forth {
            data_stack: Vec::new(),
            return_stack: Vec::new(),
            dictionary: HashMap::new(),
            words: Vec::new(),
            variables: Vec::new(), //ip: 0,
        };

        forth.add_primitive("DO", |f| {
            // copy two values from the data stack to the return stack
            if let (Some(val_a), Some(val_b)) = (f.data_stack.pop(), f.data_stack.pop()) {
                f.return_stack.push(val_b);
                f.return_stack.push(val_a);
            }
        });

        // Define primitive words
        forth.add_primitive("DUP", |f| {
            if let Some(top) = f.data_stack.last() {
                f.data_stack.push(top.clone());
            }
        });

        forth.add_primitive("2DUP", |f| {
            if let (Some(val_a), Some(val_b)) = (f.data_stack.pop(), f.data_stack.pop()) {
                f.data_stack.push(val_b.clone());
                f.data_stack.push(val_a.clone());
                f.data_stack.push(val_b);
                f.data_stack.push(val_a);
            }
        });

        forth.add_primitive("SPACES", |f| {
            if let Some(val) = f.data_stack.pop() {
                if let Cell::INT(i) = val {
                    for _ in 0..i {
                        print!(" ");
                    }
                } else {
                    panic!("Error: SPACES support only INT type");
                }
            }
        });

        forth.add_primitive("DROP", |f| {
            f.data_stack.pop();
        });

        forth.add_primitive("2DROP", |f| {
            f.data_stack.pop();
            f.data_stack.pop();
        });

        forth.add_primitive("SWAP", |f| {
            let len = f.data_stack.len();
            if len >= 2 {
                f.data_stack.swap(len - 1, len - 2);
            }
        });

        forth.add_primitive("OVER", |f| {
            if let (Some(val_a), Some(val_b)) = (f.data_stack.pop(), f.data_stack.pop()) {
                f.data_stack.push(val_b.clone());
                f.data_stack.push(val_a);
                f.data_stack.push(val_b);
            }
        });

        forth.add_primitive("I", |f| {
            // I - copies the top of return stack onto the data stack
            if let Some(value) = f.return_stack.last() {
                f.data_stack.push(value.clone());
            }
        });

        forth.add_primitive("J", |f| {
            // J -copies the third from the end element from return stack onto the data stack
            let val = f.return_stack.get(f.return_stack.len().wrapping_sub(3));
            if let Some(element) = val {
                f.data_stack.push(element.clone());
            }
        });

        forth.add_primitive("MOD", |f| {
            if let (Some(val_b), Some(val_a)) = (f.data_stack.pop(), f.data_stack.pop()) {
                use Cell::*;
                let result = match (val_a, val_b) {
                    (INT(x), INT(y)) => INT(x % y),
                    _ => INT(0),
                };
                f.data_stack.push(result);
            }
        });

        forth.add_primitive("0=", |f| {
            if let Some(val_a) = f.data_stack.pop() {
                use Cell::*;
                let result = match val_a {
                    INT(x) => BOOL(x == 0),
                    FLOAT(x) => BOOL(x == 0.0),
                    BOOL(x) => {
                        if !x {
                            BOOL(true)
                        } else {
                            BOOL(false)
                        }
                    }
                    STRING(x) => BOOL(x.is_empty()),
                };

                f.data_stack.push(result);
            }
        });

        forth.add_primitive("=", |f| {
            if let (Some(val_a), Some(val_b)) = (f.data_stack.pop(), f.data_stack.pop()) {
                use Cell::*;
                let type1 = val_a.type_name().clone();
                let type2 = val_b.type_name().clone();

                let result = match (val_a, val_b) {
                    (INT(x), INT(y)) => BOOL(x == y),
                    (INT(x), FLOAT(y)) => BOOL((x as f32) == y),
                    (FLOAT(x), INT(y)) => BOOL(x == (y as f32)),
                    (FLOAT(x), FLOAT(y)) => BOOL(x == y),

                    (STRING(s1), STRING(s2)) => BOOL(s1.eq(&s2)),

                    _ => {
                        panic!("Error: unsupported comparison of {} and {}", type1, type2);
                    }
                };

                f.data_stack.push(result);
            }
        });

        forth.add_primitive("+", |f| {
            if let (Some(val_a), Some(val_b)) = (f.data_stack.pop(), f.data_stack.pop()) {
                use Cell::*;
                let type1 = val_a.type_name().clone();
                let type2 = val_b.type_name().clone();
                let result = match (val_a, val_b) {
                    (INT(x), INT(y)) => INT(x + y),
                    (INT(x), FLOAT(y)) => FLOAT(x as f32 + y),
                    (FLOAT(x), INT(y)) => FLOAT(x + y as f32),
                    (FLOAT(x), FLOAT(y)) => FLOAT(x + y),

                    // String + anything
                    (STRING(s), INT(x)) => STRING(format!("{}{}", s, x)),
                    (STRING(s), FLOAT(x)) => STRING(format!("{}{}", s, x)),
                    (STRING(s), STRING(t)) => STRING(format!("{}{}", s, t)),
                    (STRING(s), BOOL(b)) => STRING(format!("{}{}", s, b)),

                    // Anything + String
                    (INT(x), STRING(s)) => STRING(format!("{}{}", x, s)),
                    (FLOAT(x), STRING(s)) => STRING(format!("{}{}", x, s)),
                    (BOOL(b), STRING(s)) => STRING(format!("{}{}", b, s)),

                    _ => {
                        panic!(
                            "Error: Wrong type provided to operator {} + {}!",
                            type1, type2
                        );
                    }
                };
                f.data_stack.push(result);
            }
        });

        forth.add_primitive("-", |f| {
            if let (Some(val_b), Some(val_a)) = (f.data_stack.pop(), f.data_stack.pop()) {
                use Cell::*;
                let type1 = val_a.type_name().clone();
                let type2 = val_b.type_name().clone();
                let result = match (val_a, val_b) {
                    (INT(x), INT(y)) => INT(x - y),
                    (INT(x), FLOAT(y)) => FLOAT(x as f32 - y),
                    (FLOAT(x), INT(y)) => FLOAT(x - y as f32),
                    (FLOAT(x), FLOAT(y)) => FLOAT(x - y),
                    _ => {
                        panic!(
                            "ERROR: Wrong type provided to operator {} - {}",
                            type1, type2
                        );
                    }
                };
                f.data_stack.push(result);
            }
        });

        forth.add_primitive("*", |f| {
            if let (Some(val_b), Some(val_a)) = (f.data_stack.pop(), f.data_stack.pop()) {
                use Cell::*;
                let result = match (val_a, val_b) {
                    (INT(x), INT(y)) => INT(x * y),
                    (INT(x), FLOAT(y)) => FLOAT(x as f32 * y),
                    (FLOAT(x), INT(y)) => FLOAT(x * y as f32),
                    (FLOAT(x), FLOAT(y)) => FLOAT(x * y),
                    _ => {
                        panic!("ERROR: Wrong type provided to operator *");
                    }
                };
                f.data_stack.push(result);
            }
        });

        forth.add_primitive("/", |f| {
            if let (Some(val_b), Some(val_a)) = (f.data_stack.pop(), f.data_stack.pop()) {
                use Cell::*;
                let result = match (val_a, val_b) {
                    (INT(x), INT(y)) => INT(x / y),
                    (INT(x), FLOAT(y)) => FLOAT(x as f32 / y),
                    (FLOAT(x), INT(y)) => FLOAT(x / y as f32),
                    (FLOAT(x), FLOAT(y)) => FLOAT(x / y),
                    _ => {
                        panic!("Wrong type provided to operator /");
                    }
                };
                f.data_stack.push(result);
            }
        });

        forth.add_primitive("*/", |f| {
            if let (Some(val_c), Some(val_b), Some(val_a)) =
                (f.data_stack.pop(), f.data_stack.pop(), f.data_stack.pop())
            {
                // println!("DEBUG: */ {:?} {:?} {:?}", &val_a, &val_b, &val_c);
                use Cell::*;
                let result = match (val_a, val_b, val_c) {
                    (INT(x), INT(y), INT(z)) => INT(x * y / z),
                    (INT(x), INT(y), FLOAT(z)) => FLOAT(x as f32 * y as f32 / z),
                    (INT(x), FLOAT(y), INT(z)) => FLOAT(x as f32 * y / z as f32),
                    (FLOAT(x), INT(y), INT(z)) => FLOAT(x * y as f32 / z as f32),
                    (FLOAT(x), FLOAT(y), FLOAT(z)) => FLOAT(x * y / z),
                    (INT(x), FLOAT(y), FLOAT(z)) => FLOAT(x as f32 * y / z),
                    (FLOAT(x), INT(y), FLOAT(z)) => FLOAT(x * y as f32 / z),
                    (FLOAT(x), FLOAT(y), INT(z)) => FLOAT(x * y / z as f32),
                    _ => {
                        panic!("Wrong type provided to operator */");
                    }
                };
                f.data_stack.push(result);
            }
        });

        forth.add_primitive(".", |f| {
            if let Some(val) = f.data_stack.pop() {
                print!("{}", val);
            }
        });

        forth.add_primitive("PRINT", |f| {
            if let Some(val) = f.data_stack.pop() {
                print!("{}", val);
            }
        });

        forth.add_primitive("U.R", |f| {
            // unsigned print, right justified
            // params: INT() - amout of spaces
            if let Some(value) = f.data_stack.pop() {
                use Cell::*;
                match value {
                    INT(spaces) => {
                        if let Some(value) = f.data_stack.pop() {
                            let result = match value {
                                INT(x) => fixed_right(&format!("{}", x), spaces as usize),
                                FLOAT(x) => fixed_right(&format!("{}", x), spaces as usize),
                                BOOL(b) => fixed_right(&format!("{}", b), spaces as usize),
                                STRING(s) => fixed_right(&s, spaces as usize),
                            };
                            print!("{}", result);
                        }
                    }
                    _ => {
                        panic!("Error: U.R supports only INT type as a parameter");
                    }
                }
            }
        });

        forth.add_primitive("EMIT", |f| {
            if let Some(val) = f.data_stack.pop() {
                if let Cell::INT(a) = val {
                    print!("{}", (a as u8) as char);
                } else {
                    panic!("Error: wrong type provided for function EMIT!");
                }
            }
        });

        forth.add_primitive("CR", |_| {
            // f.data_stack.push(Cell::STRING("\n".to_string()));
            println!("");
        });

        forth.add_primitive("MAX", |f| {
            if let (Some(val_b), Some(val_a)) = (f.data_stack.pop(), f.data_stack.pop()) {
                use Cell::*;
                let type1 = val_a.type_name().clone();
                let type2 = val_b.type_name().clone();
                let result = match (val_a, val_b) {
                    (INT(x), INT(y)) => INT(cmp::max(x, y)),
                    (FLOAT(x), FLOAT(y)) => FLOAT(x.max(y)),
                    (STRING(x), STRING(y)) => STRING(cmp::max(x, y)),
                    (INT(x), FLOAT(y)) => FLOAT(y.max(x as f32)),
                    (FLOAT(x), INT(y)) => FLOAT(x.max(y as f32)),
                    _ => {
                        panic!("Wrong type provided to the MAX function, value1 has type {}, and value2 has type {}.", type1, type2);
                    }
                };
                f.data_stack.push(result);
            }
        });

        forth.add_primitive("<", |f| {
            if let (Some(val_b), Some(val_a)) = (f.data_stack.pop(), f.data_stack.pop()) {
                use Cell::*;
                let type1 = val_a.type_name().clone();
                let type2 = val_b.type_name().clone();

                let result = match (val_a, val_b) {
                    (INT(x), INT(y)) => BOOL(x < y),
                    (FLOAT(x), FLOAT(y)) => BOOL(x < y),
                    (STRING(x), STRING(y)) => BOOL(x < y),
                    (INT(x), FLOAT(y)) => BOOL((x as f32) < y),
                    (FLOAT(x), INT(y)) => BOOL(x < (y as f32)),
                    _ => {
                        panic!("Wrong type provided to the '<' function, value1 has type {}, and value2 has type {}.", type1, type2);
                    }
                };
                f.data_stack.push(result);
            }
        });

        forth.add_primitive(">", |f| {
            if let (Some(val_b), Some(val_a)) = (f.data_stack.pop(), f.data_stack.pop()) {
                use Cell::*;
                let type1 = val_a.type_name().clone();
                let type2 = val_b.type_name().clone();

                let result = match (val_a, val_b) {
                    (INT(x), INT(y)) => BOOL(x > y),
                    (FLOAT(x), FLOAT(y)) => BOOL(x > y),
                    (STRING(x), STRING(y)) => BOOL(x > y),
                    (INT(x), FLOAT(y)) => BOOL((x as f32) > y),
                    (FLOAT(x), INT(y)) => BOOL(x < (y as f32)),
                    _ => {
                        panic!("Wrong type provided to the '>' function, value1 has type {}, and value2 has type {}.", type1, type2);
                    }
                };
                f.data_stack.push(result);
            }
        });

        forth.add_primitive("LEAVE", |f| {
            // LEAVE - causes the loop to end on the very next LOOP or +LOOP.
            //remove index from the return stack
            f.return_stack.pop();
            if let Some(Cell::INT(limit)) = f.return_stack.last() {
                f.return_stack.push(Cell::INT(*limit));
            }
        });

        forth.add_primitive("PAGE", |_f| {
            // PAGE - clear the screen
            // PLACEHOLDER
        });

        forth.add_primitive("QUIT", |_f| {
            // QUIT - end the program without printing ok at the end
            // PLACEHOLDER
        });

        forth.add_primitive("!", |f| {
            // ! - stores variable's value in the address, which shoudl be on the top of the stack
            if let Some(Cell::INT(addr)) = f.data_stack.pop() {
                if let Some(value) = f.data_stack.pop() {
                    if addr as usize >= f.variables.len() {
                        f.variables.push(value);
                    } else {
                        f.variables[addr as usize] = value;
                    }
                }
            }
        });

        forth.add_primitive("@", |f| {
            // @ - get variable value and put it onto stack
            if let Some(Cell::INT(addr)) = f.data_stack.pop() {
                if (addr as usize) < f.variables.len() {
                    f.data_stack.push(f.variables[addr as usize].clone());
                } else {
                    panic!("Error: cannot read variable value, the address is out of the range");
                }
            }
        });

        forth.add_primitive("+!", |f| {
            // +! - adds the given value to the contents of the given
            //      address.
            if let (Some(Cell::INT(address)), Some(value)) =
                (f.data_stack.pop(), f.data_stack.pop())
            {
                let address = address as usize;
                if address >= f.variables.len() {
                    panic!("Error: cannot get a variable, address is the out of the range");
                }
                //let var_value = &f.variables[address];
                if let Ok(result) = &f.variables[address].add(&value) {
                    f.variables[address] = result.clone();
                } else {
                    panic!("Error: Cannot execute !+, unsupported types");
                }
            }
        });

        forth
    }

    fn get_word_by_address(&self, addr: Address) -> Option<String> {
        for (key, value) in &self.dictionary {
            if *value == addr {
                return Some(key.clone());
            }
        }
        None
    }

    pub fn debug_show_words(&self) {
        for (address, word) in self.words.iter().enumerate() {
            match word {
                Word::Composite(val) => {
                    println!("{}: COMPOSITE: {:?}", address, val);
                }
                Word::Primitive(_) => {
                    print!("{}: PRIMITIVE", address);
                    if let Some(name) = self.get_word_by_address(address) {
                        print!("   {}", name);
                    }
                    println!("");
                }
                Word::JumpIfZero(addr) => {
                    println!("{}: JumpIfZero({})", address, addr);
                }
                Word::Jump(addr) => {
                    println!("{}: Jump({})", address, addr);
                }
                Word::Push(val) => {
                    println!("{}: Push({})", address, val);
                }
                Word::JumpLoop(val) => {
                    println!("{}: JumpLoop({})", address, val);
                }
                Word::JumpLoopInc(val) => {
                    println!("{}: JumpLoopInc({})", address, val);
                }
                Word::Var(addr) => {
                    print!("{}: Variable({})", address, addr);
                    if let Some(name) = self.get_word_by_address(address) {
                        print!(" => {name} = {}", self.variables[*addr]);
                    }
                    println!("");
                }
            }
        }
    }

    pub fn add_primitive<F>(&mut self, name: &str, code: F)
    where
        F: Fn(&mut Forth) + 'static,
    {
        let addr = self.words.len();
        self.words.push(Word::Primitive(Box::new(code)));
        self.dictionary.insert(name.to_string(), addr);
    }

    fn parse_word(word: &str) -> Result<Cell, String> {
        let s = word.trim();
        use Cell::*;
        // STRING
        if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
            let inner_string = &s[1..s.len() - 1];
            return Ok(STRING(inner_string.to_string()));
        }

        // BOOL
        if s.eq_ignore_ascii_case("true") {
            return Ok(BOOL(true));
        }
        if s.eq_ignore_ascii_case("false") {
            return Ok(BOOL(false));
        }

        // INT
        if let Ok(v) = s.parse::<i32>() {
            return Ok(INT(v));
        }

        // FLOAT
        if let Ok(v) = s.parse::<f32>() {
            return Ok(FLOAT(v));
        }

        Err(format!("Could not parse `{s}` into a Cell"))
    }

    fn extract_dependencies(body: &[String], funcs: &FunctionDefinition) -> Vec<String> {
        body.iter()
            .filter(|w| funcs.contains_key(w.as_str()))
            .cloned()
            .collect()
    }

    fn topo_sort(funcs: &FunctionDefinition) -> Result<Vec<String>, String> {
        let mut visiting = HashSet::new();
        let mut visited = HashSet::new();
        let mut order = Vec::new();

        fn dfs(
            name: &str,
            funcs: &FunctionDefinition,
            visiting: &mut HashSet<String>,
            visited: &mut HashSet<String>,
            order: &mut Vec<String>,
        ) -> Result<(), String> {
            if visited.contains(name) {
                return Ok(());
            }
            if !visiting.insert(name.to_string()) {
                return Err(format!(
                    "Circular dependecy detected for function '{}'",
                    name
                ));
            }

            let deps = Forth::extract_dependencies(funcs.get(name).unwrap(), funcs);

            for dep in deps {
                dfs(&dep, funcs, visiting, visited, order)?;
            }

            visiting.remove(name);
            visited.insert(name.to_string());
            order.push(name.to_string());
            Ok(())
        }

        for func in funcs.keys() {
            if !func.eq("ROOT") {
                dfs(func, funcs, &mut visiting, &mut visited, &mut order)?;
            }
        }

        Ok(order)
    }

    pub fn compile(&mut self, program: &str) -> Result<(), String> {
        let parsed = parse(program)?;
        let sorted = Forth::topo_sort(&parsed)?;

        for name in &sorted {
            let body = &parsed[name];
            let body_ref = body.iter().map(|s| s.as_str()).collect();
            self.compile_vector(name, body_ref)?;
        }

        // ROOT compiled last
        if let Some(root_body) = parsed.get("ROOT") {
            let body_ref = root_body.iter().map(|s| s.as_str()).collect();
            self.compile_vector("ROOT", body_ref)?;
        }

        Ok(())
    }

    pub fn run(&mut self) -> Result<Cell, String> {
        // get address of ROOT;
        if let Some(root_address) = self.dictionary.get("ROOT") {
            self.execute_word(*root_address)?;
        } else {
            return Err("Error: ROOT entry point is not found, there is nothig to execute".into());
        }

        let result = match self.data_stack.pop() {
            Some(val) => val,
            None => Cell::INT(0),
        };
        Ok(result)
    }

    pub fn compile_vector(&mut self, name: &str, definition: Vec<&str>) -> Result<(), String> {
        let mut addresses = Vec::new();

        // Stacks to manage unresolved IF/ELSE/THEN patches
        // the hold indices into 'addresses'
        let mut if_stack = Vec::new();
        let mut else_stack: Vec<Address> = Vec::new();
        let mut do_stack = Vec::new();
        let mut begin_stack = Vec::new();
        let mut while_stack = Vec::new();

        for (position, &word) in definition.iter().enumerate() {
            // 1. Literal values -> push a primitive that will push the Cell at runtime
            if let Ok(val) = Forth::parse_word(&word) {
                let addr = self.words.len();

                self.words.push(Word::Push(val.clone()));

                addresses.push(addr);
            } else if word.eq("BEGIN") {
                // remember addres the first word after BEGIN
                begin_stack.push(addresses.len() as i32);
            } else if word.eq("UNTIL") {
                let begin_pos = begin_stack.pop().ok_or_else(|| {
                    format!(
                        "Error: UNTIL at position {} without matching BEGIN",
                        position
                    )
                })?;
                // calcultaion offset
                let offset = begin_pos - addresses.len() as i32;
                let addr = self.words.len();

                self.words.push(Word::JumpIfZero(offset));

                addresses.push(addr);
            } else if word.eq("WHILE") {
                let addr = self.words.len();
                while_stack.push(addr);

                self.words.push(Word::JumpIfZero(0)); //put placeholder, which will be corrected by REPEAT

                addresses.push(addr);
            } else if word.eq("REPEAT") {
                if let Some(while_word_addr) = while_stack.pop() {
                    let begin_pos = begin_stack.pop().ok_or_else(|| {
                        format!(
                            "Error: REPEAT at position {} without matching BEGIN",
                            position
                        )
                    })?;

                    let begin_offset = begin_pos - addresses.len() as i32;
                    // Put REPEAT as Jump to BEGIN
                    let addr = self.words.len();
                    self.words.push(Word::Jump(begin_offset));

                    addresses.push(addr);

                    // patch While JumpIfZero word
                    match &mut self.words[while_word_addr] {
                        Word::JumpIfZero(target) => {
                            *target = addresses.len() as i32; // the next word after REPEAT/Jump
                        }
                        _ => {
                            return Err(format!(
                                "Internal error: expected JumpIfZero at address {}",
                                while_word_addr
                            ));
                        }
                    };
                } else {
                    return Err(format!(
                        "Error: REPEAT at position: {} without matching WHILE word",
                        position
                    ));
                }
            } else if word.eq("DO") {
                // put DO in addresses
                if let Some(&addr) = self.dictionary.get(word) {
                    addresses.push(addr);
                }
                // remeber address after DO
                do_stack.push(addresses.len());
            } else if word.eq("LOOP") {
                let do_pos = do_stack
                    .pop()
                    .ok_or_else(|| format!("LOOP at position {} without matching DO", position))?;
                let addr = self.words.len();

                self.words
                    .push(Word::JumpLoop(do_pos as i32 - addresses.len() as i32));

                addresses.push(addr);
            } else if word.eq("+LOOP") {
                let do_pos = do_stack
                    .pop()
                    .ok_or_else(|| format!("+LOOP at position {} witout matching DO", position))?;
                let addr = self.words.len();

                self.words
                    .push(Word::JumpLoopInc(do_pos as i32 - addresses.len() as i32));

                addresses.push(addr);
            } else if word.eq("IF") {
                // IF - emit JumpIfZero placeholder and push unresoved index on if_stack
                let addr = self.words.len();
                self.words.push(Word::JumpIfZero(0)); //0 is placeholder

                // push the index in 'addresses' so we can find it later to patch
                if_stack.push(addresses.len() as i32);

                addresses.push(addr);
            } else if word.eq("ELSE") {
                // pop the most recent IF (must exist)
                let if_pos = if_stack
                    .pop()
                    .ok_or_else(|| format!("ELSE at position {} without matching IF", position))?;

                // emit an unconditional jump placeholder for skipping the ELSE block
                let jmp_addr = self.words.len();
                self.words.push(Word::Jump(0)); // 0 is placeholder
                addresses.push(jmp_addr);

                // record this JMP for later patching by THEN
                else_stack.push(addresses.len() - 1);

                // patch the earlier IF's JumIfZero to jump to the start of the ELSE block.
                // calculate the offset
                let offset = addresses.len() as i32 - if_pos;
                let if_word_addr = addresses[if_pos as usize];
                //let else_address = self.words.len();
                match &mut self.words[if_word_addr] {
                    Word::JumpIfZero(target) => {
                        // the ELSE block starts after the JMP we just emitted,
                        // so target should be current lenght of words (the next
                        // instruction).
                        *target = offset;
                    }
                    _ => {
                        return Err(format!(
                            "Internal error: expected JumpIOfZero at address offset {}",
                            if_word_addr
                        ));
                    }
                }
            } else if word.eq("THEN") {
                if let Some(else_pos) = else_stack.pop() {
                    // we have an ELSE before: patch the JMP insert at ELSE
                    let jmp_word_addr = addresses[else_pos];
                    let offset = addresses.len() as i32 - else_pos as i32;

                    // let then_address = self.words.len();
                    match &mut self.words[jmp_word_addr] {
                        Word::Jump(target) => {
                            *target = offset;
                        }
                        _ => {
                            return Err(format!(
                                "Internal error: expected Jump at the address {}",
                                jmp_word_addr
                            ));
                        }
                    }
                } else if let Some(if_pos) = if_stack.pop() {
                    // no ELSE: patch the IF's JumpIfZero to jump to the
                    // instruction after THEN
                    let if_word_addr = addresses[if_pos as usize];
                    let offset = addresses.len() as i32 - if_pos;
                    match &mut self.words[if_word_addr] {
                        Word::JumpIfZero(target) => {
                            *target = offset;
                        }
                        _ => {
                            return Err(format!(
                                "Internal error: expected JumpIfZero at address {}",
                                if_word_addr
                            ));
                        }
                    }
                } else {
                    return Err(format!(
                        "THEN at position {} without matching IF/ELSE",
                        position
                    ));
                }
            } else if let Some(&addr) = self.dictionary.get(word) {
                addresses.push(addr);
            } else {
                //probably this is a variable
                let addr = self.words.len();

                let data_address = self.variables.len();

                // push default INT(0) to variable to reserve a slot
                self.variables.push(Cell::INT(0));

                self.dictionary.insert(word.to_string(), addr);
                self.words.push(Word::Var(data_address));

                addresses.push(addr);

                //return Err(format!("Error: Unknown word: {}", word));
            }
        }

        // after processing all tokens, ensure all IF/ELSEs DO/LOOP were closed
        if !if_stack.is_empty() {
            return Err("Error: IF without matching THEN".into());
        }
        if !else_stack.is_empty() {
            return Err("Error: ELSE without matching THEN".into());
        }

        if !do_stack.is_empty() {
            return Err("Error: DO without matching LOOP/+LOOP".into());
        }

        if !begin_stack.is_empty() {
            return Err("Error: BEGIN without matching UNTIL".into());
        }

        if !while_stack.is_empty() {
            return Err("Error: WHILE without matching REPEAT".into());
        }

        let addr = self.words.len();
        self.words.push(Word::Composite(addresses));
        self.dictionary.insert(name.to_string(), addr);

        Ok(())
    }

    pub fn execute(&mut self, name: &str) -> Result<(), String> {
        let addr = *self
            .dictionary
            .get(name)
            .ok_or_else(|| format!("Error: word not found: {}", name))?;

        self.execute_word(addr)?;
        Ok(())
    }

    // executes the word and returns offset to the next command
    fn execute_word(&mut self, addr: Address) -> Result<i32, String> {
        /*
        println!(
            "EXECUTE: {}({}) : {:?}",
            &self.words[addr],
            addr,
            self.get_word_by_address(addr)
        );
        */
        // We need to handle this carefully to avoid borrowing issues
        match &self.words[addr] {
            Word::Primitive(_) => {
                // Get a raw pointer to avoid checker issues
                let words_ptr = self.words.as_ptr();
                unsafe {
                    if let Word::Primitive(code) = &(*words_ptr.add(addr)) {
                        code(self)
                    }
                }
            }
            Word::Composite(addresses) => {
                // Clone the address to avoid borrow issues
                let addresses = addresses.clone();

                // This is the threaded code interpreter
                // Save return address
                // self.return_stack.push(Cell::INT(self.ip));

                //Execute each word in the thread
                let mut instruction_pointer: i32 = 0;
                loop {
                    let word_address = addresses[instruction_pointer as usize];
                    let offset = self.execute_word(word_address)?;
                    instruction_pointer += offset;

                    if instruction_pointer < 0 {
                        return Err("ERROR: instruction pointer is less than 0".into());
                    }

                    // instruction_pointer += 1;
                    if instruction_pointer as usize >= addresses.len() {
                        break;
                    }
                }

                // Restore return address
                // if let Some(ret_addr) = self.return_stack.pop() {
                //    let Cell::INT(self.ip) = ret_addr;
                //}
            }
            Word::JumpIfZero(offset) => {
                if let Some(value) = self.data_stack.pop() {
                    let result = match value {
                        Cell::BOOL(val) => val,
                        Cell::INT(i) => i != 0,
                        Cell::FLOAT(f) => f != 0.0,
                        Cell::STRING(s) => !s.is_empty(),
                    };
                    if !result {
                        return Ok(*offset);
                    }
                } else {
                    return Err("Error: IF support only BOOL datatype".to_string());
                }
                return Ok(1); // offset to the next command
            }
            Word::Jump(offset) => return Ok(*offset as i32),
            Word::Push(value) => {
                self.data_stack.push(value.clone());
            }
            Word::JumpLoop(offset) => {
                //get the element from the return_stack
                let index = self.return_stack.pop().ok_or_else(|| {
                    format!("Error: cannot execute LOOP as there is no index in the return stack")
                })?;
                let limit = self.return_stack.last().ok_or_else(|| {
                    format!("Error: cannot execute LOOP as there is no limit in the return stack")
                })?;

                match (index, limit) {
                    (Cell::INT(i), Cell::INT(l)) => {
                        let mut new_index = i;
                        if *l > i {
                            new_index += 1;
                        } else if *l < i {
                            new_index -= 1;
                        }
                        if new_index == *l {
                            //LOOP cycle is ended
                            //remove two last elements of return_stack
                            //the index has been already removed (see above)
                            //only limit is remained
                            self.return_stack.pop();
                            return Ok(1); // execute next command after LOOP
                        }
                        self.return_stack.push(Cell::INT(new_index));
                    }
                    _ => {
                        return Err(
                            "Error: cannot execute LOOP as index and limit should be in INT".into(),
                        );
                    }
                };

                return Ok(*offset as i32);
            }
            Word::JumpLoopInc(offset) => {
                //get the element from the return_stack
                let index = self.return_stack.pop().ok_or_else(|| {
                    format!("Error: cannot execute LOOP as there is no index in the return stack")
                })?;
                let limit = self.return_stack.last().ok_or_else(|| {
                    format!("Error: cannot execute LOOP as there is no limit in the return stack")
                })?;

                // get the increment from data stack
                if let Some(value) = self.data_stack.pop() {
                    if let Cell::INT(inc) = value {
                        match (index, limit) {
                            (Cell::INT(i), Cell::INT(l)) => {
                                let mut new_index = i;

                                if (i < *l && inc > 0) || (i > *l && inc < 0) {
                                    new_index += inc;
                                } else {
                                    return Err(
                                        "Cannot execute Incremental LOOP as increment has wrong sign (+ or -) or 0. This could lead to infinite loop."
                                            .into(),
                                    );
                                }

                                if (inc > 0 && new_index >= *l) || (inc < 0 && new_index <= *l) {
                                    //LOOP cycle is ended
                                    //remove two last elements of return_stack
                                    //the index has been already removed (see above)
                                    //only limit is remained
                                    self.return_stack.pop();
                                    return Ok(1); // execute next command after LOOP
                                }
                                self.return_stack.push(Cell::INT(new_index));
                            }
                            _ => {
                                return Err(
                                    "Error: cannot execute LOOP as index and limit should be in INT".into(),
                                );
                            }
                        };
                        return Ok(*offset as i32);
                    } else {
                        return Err(
                            "Error: cannot execute Incremental LOOP as increment should be INT"
                                .into(),
                        );
                    }
                }
            }
            Word::Var(addr) => {
                // cope variable's address to the stack
                self.data_stack.push(Cell::INT(*addr as i32));
            }
        }

        // println!("\tSTACK: {:?}", &self.data_stack);

        Ok(1)
    }

    pub fn push(&mut self, value: Cell) {
        self.data_stack.push(value);
    }
}
