// IMPORTS
use super::InputOrigin;
use super::Span;
use anyhow::*;
use nom::error::ParseError;
use regex::Regex;
use std::fs::File;
use std::path::Path;
use std::sync::Arc;
// CONSTS
// TYPES

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// Track location within a file so we know exactly where errors come from
pub struct FileLocation {
  extra: InputOrigin,
  start_line: usize,
  start_offset: usize,
  end_line: usize,
  end_offset: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// An error that knows where in the file it came from
pub struct MyError {
  location: Option<FileLocation>,
  message: Option<ErrorKind>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrorKind {
  Runtime(String),
  Parse,
  UnexpectedChar(char),
  TypeCheck(String),
  Unknown,
}

// FUNCTIONS

// TRAITS
// IMPLS

impl FileLocation {
  /// Empty file location, for test code.
  pub fn empty() -> Self {
    FileLocation {
      extra: InputOrigin::Repl(Arc::new(String::new())),
      start_line: 0,
      start_offset: 0,
      end_line: 0,
      end_offset: 0,
    }
  }
  pub fn new<'a, 'b>(start: Span<'a>, end: Option<Span<'b>>) -> Self {
    fn sub1_if_able(x: usize) -> usize {
      if x == 0 {
        x
      } else {
        x - 1
      }
    }
    let end_line = sub1_if_able(end.clone().unwrap_or(start.clone()).location_line() as usize);
    let end_offset = end.unwrap_or(start.clone()).get_column() as usize;
    Self {
      extra: start.extra.to_owned(),
      start_line: sub1_if_able(start.location_line() as usize),
      start_offset: start.get_column(),
      end_line: end_line,
      end_offset: end_offset,
    }
  }
  /// String is a nice printout of the relevnt section of the file.
  /// The section is underlined like ^~~~~~~~~~~~^.
  /// String ends in a new line.
  fn underlined_section(&self) -> Result<String> {
    // if is repl input put into lines else open file
    let lines: Vec<String> = self.extra.get_lines()?;
    let mut out = "".to_owned();
    // Case 1 start point and end point are the same
    // or start point is greater than end point.
    if (self.start_line >= self.end_line) && (self.start_offset >= self.end_offset) {
      // Add line from file
      out.push_str(
        lines
          .get(self.start_line)
          .unwrap_or(&format!("line {} out of bounds", self.start_line))
          .as_str(),
      );
      // Add underline
      let offset = if self.start_offset >= 1 {
        self.start_offset - 1
      } else {
        0
      };
      out.push_str("\n");
      out.push_str(&std::iter::repeat(" ").take(offset).collect::<String>());
      out.push_str("^\n");
    } else {
      // Case 2 start point is smaller than end point
      for line_num in self.start_line..(self.end_line + 1) {
        let line: String = lines
          .get(line_num)
          .unwrap_or(&format!("Error: line {} out of bounds", line_num))
          .to_string();
        // add line to buffer
        out.push_str(&line);
        out.push_str("\n");
        // add underline to buffer
        if line_num == self.start_line {
          // start underline
          let offset = if self.start_offset >= 1 {
            self.start_offset - 1
          } else {
            0
          };
          let rest = line.len() - usize::min(offset + 2, line.len());
          out.push_str(&std::iter::repeat(" ").take(offset).collect::<String>());
          out.push_str("^");
          out.push_str(&std::iter::repeat("~").take(rest).collect::<String>());
          // end underline  of start line and end line are the same
          if self.start_line == self.end_line {
            out.push_str("^");
          } else {
            out.push_str("~");
          }
        } else if line_num == self.end_line {
          // end underline
          let offset = if self.end_offset >= 1 {
            self.end_offset - 1
          } else {
            0
          };
          out.push_str(&std::iter::repeat("~").take(offset).collect::<String>());
          out.push_str("^");
        } else {
          // all underline
          out.push_str(&std::iter::repeat("~").take(line.len()).collect::<String>());
        }
        out.push_str("\n");
      }
    }
    return Ok(out);
  }

  /// String is a nice printout of the relevnt section of the file.
  /// The section is underlined like ^~~~~~~~~~~~^.
  /// If the file cannot be found, return "Error: no file <filename> found"
  /// or another relevent error message
  /// String ends in a new line.
  pub fn to_string(&self) -> String {
    match self.underlined_section() {
      core::result::Result::Ok(s) => s,
      Err(e) => format!("Error reading file \"{}\" {e}.\n", self.file_name()),
    }
  }
  /// Returns the origen of the input
  pub fn extra(&self) -> InputOrigin {
    self.extra.clone()
  }

  /// Returns the name of the file
  pub fn file_name(&self) -> String {
    match &self.extra {
      InputOrigin::Repl(_) => "repl input".to_owned(),
      InputOrigin::File(file) => file.to_string(),
    }
  }
}

impl MyError {
  pub const fn new(message: ErrorKind, location: FileLocation) -> Self {
    Self {
      location: Some(location),
      message: Some(message),
    }
  }

  pub fn new_from_span<'a, 'b>(
    message: ErrorKind,
    span1: Span<'a>,
    span2: Option<Span<'b>>,
  ) -> Self {
    Self {
      location: Some(FileLocation::new(span1, span2)),
      message: Some(message),
    }
  }

  pub const fn unknown_error() -> Self {
    Self {
      location: None,
      message: None,
    }
  }

  /// Turns the Error to a string
  pub fn to_string(&self) -> String {
    let message: String = match self.message() {
      ErrorKind::Runtime(s) => format!("Runtime Error \"{}\"", s),
      ErrorKind::Parse => "Parse Error".to_owned(),
      ErrorKind::UnexpectedChar(c) => format!("Parse Error, unexpected charector \"{}\"", c),
      ErrorKind::TypeCheck(t) => format!("Type Check Error \"{}\"", t),
      ErrorKind::Unknown => "Unknown Error".to_owned(),
    };
    match &self.location {
      Some(location) => {
        let file_part = location.to_string();
        // Test for Repl input
        match location.extra() {
          InputOrigin::File(file_name) => {
            let file_name = location.file_name();
            return format!("Error in file \"{file_name}\"\n{file_part}{message}");
          }
          InputOrigin::Repl(_) => {
            return format!("Error in input\n{file_part}{message}");
          }
        }
      }
      None => format! {"Error in unknown file: {message}"},
    }
  }

  pub fn message(&self) -> ErrorKind {
    match &self.message {
      Some(e) => e.clone(),
      None => ErrorKind::Unknown,
    }
  }
}

// Makes MyError nom-compatable.
// stole from: https://iximiuz.com/en/posts/rust-writing-parsers-with-nom/
impl<'a> nom::error::ParseError<Span<'a>> for MyError {
  fn from_error_kind(input: Span<'a>, _kind: nom::error::ErrorKind) -> Self {
    Self::new(ErrorKind::Parse, FileLocation::new(input, None))
  }

  fn append(_input: Span<'a>, _kind: nom::error::ErrorKind, other: Self) -> Self {
    other
  }

  fn from_char(input: Span<'a>, c: char) -> Self {
    Self::new(ErrorKind::UnexpectedChar(c), FileLocation::new(input, None))
  }
}

impl std::fmt::Display for MyError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.to_string())
  }
}

impl<'a> std::error::Error for MyError {}
// TESTS
