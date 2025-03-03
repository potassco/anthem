use {
    crate::verifying::problem::Problem,
    lazy_static::lazy_static,
    regex::Regex,
    std::{
        fmt::{Debug, Display},
        str::FromStr,
        sync::mpsc::channel,
    },
    thiserror::Error,
    threadpool::ThreadPool,
};

pub mod vampire;

lazy_static! {
    static ref STATUS: Regex =
        Regex::new(r"SZS status (?<status>[[:word:]]+) for (?<problem>[[:word:]]*)").unwrap();
}

#[derive(Debug, Error)]
pub enum StatusExtractionError {
    #[error("the status of verifying this problem is missing")]
    Missing,
    #[error("the status of verifying this problem is not recognized: `{0}`")]
    Unknown(String),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Success {
    Theorem,
    CounterSatisfiable,
    ContradictoryAxioms,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Failure {
    TimeOut,
    MemoryOut,
    GaveUp,
    // UserTerminated,
    Error,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Status {
    Success(Success),
    Failure(Failure),
}

impl Display for Status {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Status::Success(Success::Theorem) => "Theorem",
                Status::Success(Success::CounterSatisfiable) => "CounterSatisfiable",
                Status::Success(Success::ContradictoryAxioms) => "ContradictoryAxioms",
                Status::Failure(Failure::TimeOut) => "Timeout",
                Status::Failure(Failure::MemoryOut) => "MemoryOut",
                Status::Failure(Failure::GaveUp) => "GaveUp",
                Status::Failure(Failure::Error) => "Error",
            }
        )
    }
}

impl FromStr for Status {
    type Err = StatusExtractionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (_line, [status, _problem]) = STATUS
            .captures(s)
            .ok_or(StatusExtractionError::Missing)?
            .extract();

        match status {
            "Theorem" => Ok(Self::Success(Success::Theorem)),
            "CounterSatisfiable" => Ok(Self::Success(Success::CounterSatisfiable)),
            "ContradictoryAxioms" => Ok(Self::Success(Success::ContradictoryAxioms)),
            "Timeout" => Ok(Self::Failure(Failure::TimeOut)),
            "MemoryOut" => Ok(Self::Failure(Failure::MemoryOut)),
            "GaveUp" => Ok(Self::Failure(Failure::GaveUp)),
            "Error" => Ok(Self::Failure(Failure::Error)),
            x => Err(StatusExtractionError::Unknown(x.to_string())),
        }
    }
}

pub trait Report: Display + Debug + Clone {
    fn status(&self) -> Result<Status, StatusExtractionError>;
}

pub trait Prover: Debug + Clone + Send + 'static {
    type Report: Report + Send;
    type Error: Send;

    fn instances(&self) -> usize;

    fn cores(&self) -> usize;

    fn prove(&self, problem: Problem) -> Result<Self::Report, Self::Error>;

    fn prove_all(
        &self,
        problems: impl IntoIterator<Item = Problem> + 'static,
    ) -> Box<dyn Iterator<Item = Result<Self::Report, Self::Error>>> {
        if self.instances() == 1 {
            let prover = self.clone();
            Box::new(
                problems
                    .into_iter()
                    .map(move |problem| prover.prove(problem)),
            )
        } else {
            let pool = ThreadPool::new(self.instances());
            let (tx, rx) = channel();

            for problem in problems {
                let prover = self.clone();
                let tx = tx.clone();

                pool.execute(move || {
                    let result = prover.prove(problem);
                    tx.send(result).unwrap();
                })
            }

            Box::new(rx.into_iter())
        }
    }
}
