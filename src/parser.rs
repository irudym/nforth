use std::collections::HashMap;

pub type FunctionDefinition = HashMap<String, Vec<String>>;

pub fn parse(program: &str) -> Result<FunctionDefinition, String> {
    let mut functions: FunctionDefinition = HashMap::new();

    functions.insert("ROOT".into(), Vec::new());

    let tokens = tokenizer(program)?;
    let mut i = 0;

    while i < tokens.len() {
        match tokens[i].as_str() {
            ":" => {
                // function definition
                i += 1;
                if i >= tokens.len() {
                    return Err("Expected function name after ':'".into());
                }

                let func_name = tokens[i].clone();
                i += 1;

                let mut body = Vec::new();

                while i < tokens.len() && tokens[i] != ";" {
                    body.push(tokens[i].clone());
                    i += 1;
                }

                if i == tokens.len() {
                    return Err(format!("Function '{func_name}' missing ';' terminator"));
                }

                // skip the ';'
                i += 1;

                functions.insert(func_name, body);
            }

            other => {
                // ROOT level code
                functions.get_mut("ROOT").unwrap().push(other.to_string());
                i += 1;
            }
        }
    }

    Ok(functions)
}

fn tokenizer(input: &str) -> Result<Vec<String>, String> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();
    let mut position = 0;

    while let Some(&c) = chars.peek() {
        match c {
            '(' => {
                // skip comments
                chars.next();
                position += 1;
                while let Some(&ch) = chars.peek() {
                    chars.next();
                    position += 1;
                    if ch == ')' {
                        break;
                    }
                }
            }
            '.' => {
                chars.next(); // consume '.'

                // Case 1: ."
                if chars.peek() == Some(&'"') {
                    let string_pos = position;
                    let mut closed = false;

                    chars.next(); // consume the quote
                    position += 1;

                    let mut s = String::new();
                    while let Some(ch) = chars.next() {
                        if ch == '"' {
                            closed = true;
                            break;
                        }
                        s.push(ch);
                    }

                    if !closed {
                        return Err(format!(
                            "Error: string literal at position '{}' is not closed",
                            string_pos
                        ));
                    }

                    tokens.push(format!("\"{}\"", s));
                    tokens.push("PRINT".into());
                    continue;
                }

                // Case 2: Float number like 2.5 or .5
                if let Some(&next) = chars.peek() {
                    if next.is_ascii_digit() {
                        // float of form `.5`
                        let mut tok = String::from(".");
                        while let Some(ch) = chars.peek().cloned() {
                            if ch.is_ascii_digit() {
                                tok.push(ch);
                                chars.next();
                            } else {
                                break;
                            }
                        }
                        tokens.push(tok);
                        continue;
                    }
                }

                // Look back: if last token was digits, merge into a float like 2.5
                if let Some(last) = tokens.last_mut() {
                    if last.chars().all(|d| d.is_ascii_digit()) {
                        // continuing a float number
                        last.push('.');
                        // now collect fractional part
                        while let Some(ch) = chars.peek().cloned() {
                            if ch.is_ascii_digit() {
                                last.push(ch);
                                chars.next();
                            } else {
                                break;
                            }
                        }
                        continue;
                    }
                }

                // Case 3: Single '.' operator
                tokens.push(".".into());
            }
            '"' => {
                // string literal
                let string_pos = position;
                // skip
                chars.next();
                position += 1;

                let mut literal = String::new();
                let mut closed = false;

                while let Some(&ch) = chars.peek() {
                    chars.next();
                    position += 1;

                    if ch == '"' {
                        closed = true;
                        break;
                    }
                    literal.push(ch);
                }
                if !closed {
                    return Err(format!(
                        "Error: string literal at position '{}' is not closed",
                        string_pos
                    ));
                }

                tokens.push(format!("\"{}\"", literal));
            }

            c if c.is_whitespace() => {
                chars.next();
                position += 1;
            }

            _ => {
                //regular word
                let mut word = String::new();

                while let Some(&ch) = chars.peek() {
                    if ch.is_whitespace() || ch == '(' || ch == '"' {
                        break;
                    }
                    word.push(ch);
                    chars.next();
                }

                tokens.push(word);
            }
        }
    }

    Ok(tokens)
}
