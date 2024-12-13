//! # Sill: A Lisp-Like Dialect Interpreter and Transpiler Library
//! 
//! `Sill` is a library for interpreting and transpiling a Lisp-like dialect into Rust code. 
//! It provides tools for evaluating expressions, defining functions, managing environments, and generating equivalent Rust code.
//! 
//! ## Features
//! - Turing completeness with recursion and conditional expressions.
//! - Support for variable bindings and function definitions.
//! - Interoperability with Rust by transpiling `Sill` code into valid Rust functions.
//! - Simple and extensible API for embedding the interpreter in Rust programs.
//! 
//! ## Getting Started
//! 
//! Add the `Sill` library to your project dependencies:
//! 
//! ```toml
//! [dependencies]
//! sill = "0.1.0"
//! ```
//! 
//! ### Example Usage
//! 
//! ```rust
//! use sill::{Interpreter, tokenize, parse};
//! 
//! let mut interpreter = Interpreter::new();
//! let tokens = tokenize("(defn add [x y] (+ x y))");
//! let expr = parse(&tokens);
//! interpreter.evaluate(expr);
//! let result = interpreter.evaluate(parse(&tokenize("(add 3 4)")));
//! println!("Result: {:?}", result);
//! ```
//! 
//! ## Module Overview
//! - `Expr`: Core data structure representing `Sill` expressions.
//! - `Interpreter`: Provides evaluation and environment management.
//! - `parse` and `tokenize`: Utilities for parsing and tokenizing input.
//! - `transpile_to_rust`: Converts `Sill` expressions into Rust code.

use std::collections::HashMap;

/// Represents a `Sill` expression.
#[derive(Debug, Clone)]
enum Expr {
    /// A numeric literal.
    Number(i32),
    /// A symbol (identifier).
    Symbol(String),
    /// A list of expressions.
    List(Vec<Expr>),
}

/// The `Interpreter` struct manages the evaluation environment and provides methods for evaluating and transpiling expressions.
pub struct Interpreter {
    /// The environment is a mapping of variable and function names to their corresponding `Expr` values.
    environment: HashMap<String, Expr>,
}

impl Interpreter {
    /// Creates a new, empty `Interpreter` instance.
    /// 
    /// # Returns
    /// A new `Interpreter` with an empty environment.
    pub fn new() -> Self {
        Interpreter {
            environment: HashMap::new(),
        }
    }

    /// Evaluates a `Sill` expression in the current environment.
    /// 
    /// # Parameters
    /// - `expr`: The expression to evaluate.
    /// 
    /// # Returns
    /// The result of the evaluation as an `Expr`.
    /// 
    /// # Panics
    /// This function panics if the evaluation encounters unsupported operations or malformed expressions.
    pub fn evaluate(&mut self, expr: Expr) -> Expr {
        match expr {
            Expr::Number(_) => expr,
            Expr::Symbol(sym) => self.environment.get(&sym).cloned().unwrap_or(Expr::Symbol(sym)),
            Expr::List(list) => {
                if list.is_empty() {
                    panic!("Empty list encountered");
                }

                let first = &list[0];
                match first {
                    Expr::Symbol(sym) if sym == "defn" => {
                        // (defn name [args] body)
                        let name = match &list[1] {
                            Expr::Symbol(s) => s.clone(),
                            _ => panic!("Expected function name"),
                        };
                        let args = match &list[2] {
                            Expr::List(args) => args.clone(),
                            _ => panic!("Expected argument list"),
                        };
                        let body = list[3].clone();
                        self.environment.insert(
                            name.clone(),
                            Expr::List(vec![Expr::Symbol("fn".into()), Expr::List(args), body]),
                        );
                        Expr::Symbol("Function defined".into())
                    }
                    Expr::Symbol(sym) if sym == "let" => {
                        // (let [var val] body)
                        if let Expr::List(bindings) = &list[1] {
                            if bindings.len() == 2 {
                                let var = match &bindings[0] {
                                    Expr::Symbol(v) => v.clone(),
                                    _ => panic!("Expected variable name"),
                                };
                                let value = self.evaluate(bindings[1].clone());
                                self.environment.insert(var, value);
                                self.evaluate(list[2].clone())
                            } else {
                                panic!("Invalid let bindings");
                            }
                        } else {
                            panic!("Invalid let format");
                        }
                    }
                    Expr::Symbol(sym) if sym == "if" => {
                        // (if cond then else)
                        let cond = self.evaluate(list[1].clone());
                        match cond {
                            Expr::Number(n) if n != 0 => self.evaluate(list[2].clone()),
                            _ => self.evaluate(list[3].clone()),
                        }
                    }
                    Expr::Symbol(sym) if sym == "println" => {
                        let evaluated = self.evaluate(list[1].clone());
                        match evaluated {
                            Expr::Number(n) => println!("{}", n),
                            Expr::Symbol(s) => println!("{}", s),
                            _ => println!("Unknown"),
                        }
                        Expr::Symbol("Printed".into())
                    }
                    Expr::Symbol(sym) if sym == "fn" => {
                        let args = match &list[1] {
                            Expr::List(a) => a.clone(),
                            _ => panic!("Expected argument list"),
                        };
                        let body = list[2].clone();
                        Expr::List(vec![Expr::Symbol("fn".into()), Expr::List(args), body])
                    }
                    Expr::Symbol(sym) => {
                        if let Some(Expr::List(func)) = self.environment.get(sym) {
                            if func.len() == 3 && matches!(&func[0], Expr::Symbol(s) if s == "fn") {
                                let args = match &func[1] {
                                    Expr::List(a) => a,
                                    _ => panic!("Invalid function arguments"),
                                };
                                if args.len() != list.len() - 1 {
                                    panic!("Argument count mismatch");
                                }
                                let body = &func[2];
                                let mut local_env = self.environment.clone();
                                for (arg, val) in args.iter().zip(&list[1..]) {
                                    if let Expr::Symbol(arg_name) = arg {
                                        local_env.insert(arg_name.clone(), self.evaluate(val.clone()));
                                    } else {
                                        panic!("Invalid argument name");
                                    }
                                }
                                let mut local_interpreter = Interpreter {
                                    environment: local_env,
                                };
                                local_interpreter.evaluate(body.clone())
                            } else {
                                panic!("Invalid function call");
                            }
                        } else {
                            panic!("Undefined function: {}", sym);
                        }
                    }
                    _ => panic!("Unknown list operation"),
                }
            }
        }
    }

    /// Transpiles a `Sill` expression into Rust code.
    /// 
    /// # Parameters
    /// - `expr`: The expression to transpile.
    /// 
    /// # Returns
    /// A `String` containing the Rust equivalent of the `Sill` expression.
    /// 
    /// # Panics
    /// This function panics if it encounters unsupported expressions or structures during transpilation.
    pub fn transpile_to_rust(&self, expr: Expr) -> String {
        match expr {
            Expr::Number(n) => n.to_string(),
            Expr::Symbol(sym) => sym,
            Expr::List(list) => {
                if list.is_empty() {
                    panic!("Empty list cannot be transpiled");
                }

                let first = &list[0];
                match first {
                    Expr::Symbol(sym) if sym == "defn" => {
                        // (defn name [args] body)
                        let name = match &list[1] {
                            Expr::Symbol(s) => s.clone(),
                            _ => panic!("Expected function name"),
                        };
                        let args = match &list[2] {
                            Expr::List(args) => args
                                .iter()
                                .map(|arg| match arg {
                                    Expr::Symbol(a) => a.clone(),
                                    _ => panic!("Invalid argument name"),
                                })
                                .collect::<Vec<_>>()
                                .join(", ");
                        args
                        };
                        let body = self.transpile_to_rust(list[3].clone());
                        format!("fn {}({}) -> i32 {{ {} }}", name, args, body)
                    }
                    _ => panic!("Unsupported transpilation"),
                }
            }
        }
    }
}

/// Parses a sequence of tokens into a `Sill` expression.
/// 
/// # Parameters
/// - `tokens`: A slice of string tokens representing the input.
/// 
/// # Returns
/// An `Expr` representing the parsed structure.
/// 
/// # Panics
/// This function panics if the token sequence is invalid.
pub fn parse(tokens: &[&str]) -> Expr {
    if tokens.len() == 1 {
        if let Ok(number) = tokens[0].parse::<i32>() {
            Expr::Number(number)
        } else {
            Expr::Symbol(tokens[0].to_string())
        }
    } else if tokens[0] == "(" {
        let mut list = Vec::new();
        let mut depth = 0;
        let mut sub_tokens = Vec::new();
        for &token in &tokens[1..] {
            if token == "(" {
                depth += 1;
                sub_tokens.push(token);
            } else if token == ")" {
                if depth == 0 {
                    if !sub_tokens.is_empty() {
                        list.push(parse(&sub_tokens));
                        sub_tokens.clear();
                    }
                    break;
                } else {
                    depth -= 1;
                    sub_tokens.push(token);
                }
            } else {
                if depth > 0 {
                    sub_tokens.push(token);
                } else {
                    list.push(parse(&[token]));
                }
            }
        }
        Expr::List(list)
    } else {
        panic!("Unexpected token sequence: {:?}", tokens);
    }
}

/// Tokenizes an input string into a sequence of tokens for parsing.
/// 
/// # Parameters
/// - `input`: The raw input string.
/// 
/// # Returns
/// A `Vec<&str>` containing the individual tokens.
pub fn tokenize(input: &str) -> Vec<&str> {
    input
        .replace("(", " ( ")
        .replace(")", " ) ")
        .split_whitespace()
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_interpreter() {
        let mut interpreter = Interpreter::new();
        let tokens = tokenize("(defn add [x y] (+ x y))");
        let expr = parse(&tokens);
        let result = interpreter.evaluate(expr);
        assert_eq!(result, Expr::Symbol("Function defined".to_string()));
    }
}