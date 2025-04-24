use {
    anyhow::{Context as _, Result},
    std::{
        fmt::{Debug, Display},
        fs::{self, File},
        hash::Hash,
        io::{self, Write as _, stdin},
        path::Path,
        str::FromStr,
    },
};

pub mod asp;
pub mod fol;

pub trait Node: Clone + Debug + Eq + PartialEq + FromStr + Display + Hash {
    fn from_stdin() -> Result<Self>
    where
        <Self as FromStr>::Err: std::error::Error + Sync + Send + 'static,
    {
        io::read_to_string(stdin())
            .with_context(|| "could not read from stdin")?
            .parse()
            .with_context(|| "could not parse content from stdin")
    }

    fn from_file<P: AsRef<Path>>(path: P) -> Result<Self>
    where
        <Self as FromStr>::Err: std::error::Error + Sync + Send + 'static,
    {
        let path = path.as_ref();
        fs::read_to_string(path)
            .with_context(|| format!("could not read file `{}`", path.display()))?
            .parse()
            .with_context(|| format!("could not parse file `{}`", path.display()))
    }

    fn to_file<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let path = path.as_ref();
        let mut file = File::create(path)
            .with_context(|| format!("could not create file `{}`", path.display()))?;
        write!(file, "{self}").with_context(|| format!("could not write file `{}`", path.display()))
    }
}

macro_rules! impl_node {
    ($node:ty, $format:expr, $parser:ty) => {
        impl Node for $node {}

        impl std::fmt::Display for $node {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", $format(self))
            }
        }

        impl std::str::FromStr for $node {
            type Err = <$parser as crate::parsing::Parser>::Error;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                <$parser as crate::parsing::Parser>::parse(s)
            }
        }
    };
}

pub(crate) use impl_node;
