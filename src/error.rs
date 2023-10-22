use std::{
    error::Error,
    fmt::{self, Debug, Display},
    io,
};

#[allow(clippy::exhaustive_structs)]
#[derive(Debug)]
/// Represents an [`io::Error`] when trying to convert an object to a pages object, while also
/// containg the object the operation was attempted on
pub struct IntoPagesError<T: Debug> {
    /// The [`io::Error`] that occured when attempting the operation
    pub err: io::Error,
    /// The object the operation was attempted on
    pub from: T,
}

#[allow(clippy::exhaustive_structs)]
#[derive(Debug)]
/// Represents an error when trying to join multiple pages objects into 1, while also containing
/// the pages which were attempted to be joined.
pub struct JoinError<T: Debug> {
    /// Contains the specific error that occured when attempting the operation
    pub kind: JoinErrorKind,
    /// Contains the different pages that were trying to be joined
    pub parts: T,
}

#[allow(clippy::exhaustive_enums)]
#[derive(Debug)]
/// Represents the different errors that could occur when trying to join pages objects
pub enum JoinErrorKind {
    /// An [`io::Error`] occured when trying to apply the correct protection to the newly joined
    /// pages
    IO(io::Error),
    /// The pages that were trying to be joined were not part of the same allocation or were not
    /// contiguous
    NonContiguous,
}

impl<T: Debug> Display for IntoPagesError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Error converting...\n")?;
        Debug::fmt(&self.from, f)?;
        f.write_str("\n... into a Pages object:\n")?;
        Display::fmt(&self.err, f)
    }
}

#[allow(clippy::missing_trait_methods)]
impl<T: Debug> Error for IntoPagesError<T> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&self.err)
    }
}

impl<T: Debug> Display for JoinError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Error joining...\n")?;
        Debug::fmt(&self.parts, f)?;
        f.write_str("\n... ")?;
        Display::fmt(&self.kind, f)
    }
}

#[allow(clippy::missing_trait_methods)]
impl<T: Debug> Error for JoinError<T> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self.kind {
            JoinErrorKind::NonContiguous => None,
            JoinErrorKind::IO(ref e) => Some(e),
        }
    }
}

impl Display for JoinErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::NonContiguous => {
                f.write_str("Provided pages are not contiguous or belong to different allocations")
            }
            Self::IO(ref e) => Display::fmt(e, f),
        }
    }
}
