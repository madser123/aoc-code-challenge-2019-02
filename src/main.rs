#![allow(clippy::missing_errors_doc, clippy::missing_panics_doc)]

use std::{fmt::Display, num::ParseIntError, path::Path, str::FromStr};

/// An error from the Intcode computer
#[derive(Debug)]
pub enum Error {
    IntParsing(ParseIntError),
    InvalidInstruction(usize),
    Reading(std::io::Error),
}
impl std::error::Error for Error {}
impl Display for Error {
    /// Displays the error
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let error = match self {
            Self::IntParsing(error) => format!("Failed to parse integer from input! {error}"),
            Self::InvalidInstruction(code) => format!("Invalid instruction op-code '{code}'"),
            Self::Reading(error) => format!("Failed to read input! {error}"),
        };

        write!(f, "Intcode Error: {error}")
    }
}

/// An instruction for an int-code program
#[derive(PartialEq, Eq)]
enum Instruction {
    Add { a: usize, b: usize, address: usize },
    Mul { a: usize, b: usize, address: usize },
    Halt,
}

impl TryFrom<&[usize]> for Instruction {
    type Error = Error;

    fn try_from(value: &[usize]) -> Result<Self, Self::Error> {
        match value[0] {
            1 => Ok(Self::Add {
                a: value[1],
                b: value[2],
                address: value[3],
            }),
            2 => Ok(Self::Mul {
                a: value[1],
                b: value[2],
                address: value[3],
            }),
            99 => Ok(Self::Halt),
            i => Err(Error::InvalidInstruction(i)),
        }
    }
}

/// An int-code program
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntCode {
    memory: Vec<usize>,
}
impl Display for IntCode {
    /// Prints the code in a human-readable way
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let code = self
            .memory
            .chunks(4)
            .enumerate()
            .map(|(index, chunk)| format!("{index}: {chunk:?}"))
            .collect::<Vec<String>>()
            .join("\n");

        write!(f, "{code}")
    }
}
impl FromStr for IntCode {
    type Err = Error;

    /// Creates a new program from a str
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let memory = s
            .split(',')
            .map(Self::parse_single)
            .collect::<Result<Vec<usize>, Error>>()?;
        Ok(Self { memory })
    }
}
impl IntCode {
    /// Creates a new program from a file
    pub fn from_path<P>(path: P) -> Result<Self, Error>
    where
        P: AsRef<Path>,
    {
        let input = std::fs::read_to_string(path).map_err(Error::Reading)?;
        Self::from_str(&input)
    }

    /// Changes the inputs of the program
    #[must_use]
    pub fn with_inputs(mut self, noun: usize, verb: usize) -> Self {
        self.memory[1] = noun;
        self.memory[2] = verb;
        self
    }

    /// Runs the program
    pub fn run(&mut self) -> usize {
        let mut index = 0;
        while index < self.memory.len() {
            match Instruction::try_from(&self.memory[index..=index + 3]).expect("Program encountered an error") {
                Instruction::Halt => break,
                Instruction::Add { a, b, address } => self.replace_value(address, self.get(a) + self.get(b)),
                Instruction::Mul { a, b, address } => self.replace_value(address, self.get(a) * self.get(b)),
            };

            index += 4;
        }

        // Return the result
        self.get(0).to_owned()
    }

    /// Gets a value from the program
    #[must_use]
    pub fn get(&self, address: usize) -> &usize {
        self.memory
            .get(address)
            .expect("No value at address '{index}'")
    }

    /// Parses a single value from a str to usize
    fn parse_single(single: &str) -> Result<usize, Error> {
        single
            .parse()
            .map_err(Error::IntParsing)
    }

    /// Replaces a value in memory
    fn replace_value(&mut self, address: usize, new_value: usize) {
        self.memory[address] = new_value;
    }
}

fn main() {
    let one = solution_one();
    let two = solution_two();
    println!("Solution one: {one} | Solution two: {two}");
}

#[must_use]
pub fn solution_one() -> usize {
    let code = IntCode::from_path("input.txt").expect("Failed to instantiate code");
    code.with_inputs(12, 2).run()
}

#[must_use]
pub fn solution_two() -> usize {
    let code = IntCode::from_path("input.txt").expect("Failed to instantiate code");
    for noun in 0..=99 {
        for verb in 0..=99 {
            if code
                .clone()
                .with_inputs(noun, verb)
                .run()
                == 19_690_720
            {
                return 100 * noun + verb;
            }
        }
    }
    panic!("No value found for solution two!")
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use super::IntCode;

    #[test]
    fn example() {
        let mut code = IntCode::from_str("1,9,10,3,2,3,11,0,99,30,40,50").expect("Failed to instantiate code");
        code.run();
        assert_eq!(
            code,
            IntCode::from_str("3500,9,10,70,2,3,11,0,99,30,40,50").expect("Failed to instantiate test-data.")
        );
    }

    #[test]
    fn add_and_exit() {
        let mut code = IntCode::from_str("1,0,0,0,99").expect("Failed to instantiate code");
        code.run();
        assert_eq!(
            code,
            IntCode::from_str("2,0,0,0,99").expect("Failed to instantiate test-data.")
        );
    }

    #[test]
    fn add_and_exit_big() {
        let mut code = IntCode::from_str("1,1,1,4,99,5,6,0,99").expect("Failed to instantiate code");
        code.run();
        assert_eq!(
            code,
            IntCode::from_str("30,1,1,4,2,5,6,0,99").expect("Failed to instantiate test-data.")
        );
    }

    #[test]
    fn mul_and_exit() {
        let mut code = IntCode::from_str("2,3,0,3,99").expect("Failed to instantiate code");
        code.run();
        assert_eq!(
            code,
            IntCode::from_str("2,3,0,6,99").expect("Failed to instantiate test-data.")
        );
    }

    #[test]
    fn mul_and_exit_big() {
        let mut code = IntCode::from_str("2,4,4,5,99,0").expect("Failed to instantiate code");
        code.run();
        assert_eq!(
            code,
            IntCode::from_str("2,4,4,5,99,9801").expect("Failed to instantiate test-data.")
        );
    }
}
