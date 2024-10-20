//! Support MVCC (Multiple Version Concurrent Control) for `crossbeam-skiplist`.
#![forbid(unsafe_code)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]

/// A multiple version ordered map based on a lock-free skip list. See [`SkipMap`].
mod map;
pub use map::*;
