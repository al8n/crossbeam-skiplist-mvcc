#![doc = include_str!("../README.md")]
#![forbid(unsafe_code)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]

/// A multiple version ordered map based on a lock-free skip list. See [`SkipMap`](crate::nested::SkipMap).
pub mod nested;

/// A multiple version ordered map based on a lock-free skip list. See [`SkipMap`](crate::flatten::SkipMap).
pub mod flatten;
