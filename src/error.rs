use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    Lowlevel(String),
    Recov(String),
    Parse(String),
    Decoder(String),
    BadData(String),
    Unimpl { message: String, instruction_length: i32 },
    DataUnavail(String),
    Evaluation(String),
    Sleigh(String),
    JumptableThunk(String),
    ParamUnassigned(String),
    DuplicateFunction { address: String, function_name: String },
}

pub type Result<T> = std::result::Result<T, Error>;

impl Error {
    pub fn explain(&self) -> &str {
        match self {
            Error::Lowlevel(message)
            | Error::Recov(message)
            | Error::Parse(message)
            | Error::Decoder(message)
            | Error::BadData(message)
            | Error::DataUnavail(message)
            | Error::Evaluation(message)
            | Error::Sleigh(message)
            | Error::JumptableThunk(message)
            | Error::ParamUnassigned(message) => message,
            Error::Unimpl { message, .. } => message,
            Error::DuplicateFunction { .. } => "Duplicate Function",
        }
    }

    pub fn is_lowlevel(&self) -> bool {
        !matches!(self, Error::Decoder(_))
    }

    pub fn is_recov(&self) -> bool {
        matches!(self, Error::Recov(_) | Error::DuplicateFunction { .. })
    }
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.explain())
    }
}

impl std::error::Error for Error {}
