use std::fmt::Display;

#[derive(Debug, Eq, PartialEq)]
pub struct WithWarnings<D, W> {
    pub data: D,
    pub warnings: Vec<W>,
}

impl<D, W> WithWarnings<D, W> {
    pub fn flawless(data: D) -> Self {
        WithWarnings {
            data,
            warnings: Vec::new(),
        }
    }

    pub fn add_warning(mut self, warning: W) -> Self {
        self.warnings.push(warning);
        self
    }

    pub fn preface_warnings(mut self, mut warnings: Vec<W>) -> Self {
        warnings.append(&mut self.warnings);
        self.warnings = warnings;
        self
    }
}

impl<D, W: Display> WithWarnings<D, W> {
    pub fn report_warnings(self) -> D {
        for warning in self.warnings {
            println!("{warning}");
        }
        self.data
    }
}

pub type Result<D, W, E> = std::result::Result<WithWarnings<D, W>, E>;
