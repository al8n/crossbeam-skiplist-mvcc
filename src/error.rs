/// Errors for multiple version `SkipMap`s
#[derive(Debug, Clone)]
pub enum Error {
  /// Returned when trying to insert an entry with a version that already been discarded.
  AlreadyDiscarded(u64),
}

impl core::fmt::Display for Error {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::AlreadyDiscarded(version) => write!(
        f,
        "version({version}) has already been discarded by compaction"
      ),
    }
  }
}

impl core::error::Error for Error {}
