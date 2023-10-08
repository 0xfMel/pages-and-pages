use std::io;

#[allow(clippy::exhaustive_structs)]
#[derive(Debug)]
/// Represents an `io::Error` when trying to convert an object to a pages object, while also
/// containg the object the operation was attempted on
pub struct IntoPagesError<T> {
    /// The `io::Error` that occured when attempting the operation
    pub err: io::Error,
    /// The object the operation was attempted on
    pub from: T,
}

#[allow(clippy::exhaustive_structs)]
#[derive(Debug)]
/// Represents an error when trying to join multiple pages objects into 1, while also containing
/// the pages which were attempted to be joined.
pub struct JoinError<T> {
    /// Contains the specific error that occured when attempting the operation
    pub kind: JoinErrorKind,
    /// Contains the different pages that were trying to be joined
    pub parts: T,
}

#[allow(clippy::exhaustive_enums)]
#[derive(Debug)]
/// Represents the different errors that could occur when trying to join pages objects
pub enum JoinErrorKind {
    /// An `io::Error` occured when trying to apply the correct protection to the newly joined
    /// pages
    IO(io::Error),
    /// The pages that were trying to be joined were not part of the same allocation or were not
    /// contiguous
    NonContiguous,
}
