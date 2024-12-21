use dbutils::{
  equivalentor::Ascend,
  state::{Active, MaybeTombstone, State},
};
use snapshotor::{dedup, valid, Builder, NoopValidator};

use crate::sealed::TombstoneValidator;

use super::{entry::MapEntry, Entry, SkipMap};

/// The state of the iterator.
pub trait IterState<K, V>: sealed::Sealed<K, V> {}

impl<K, V, T> IterState<K, V> for T where T: sealed::Sealed<K, V> {}

mod sealed {
  use super::*;

  pub trait Sealed<K, V>: State {
    type Iter<'a>;
  }

  impl<K, V> Sealed<K, V> for Active
  where
    K: 'static,
    V: 'static,
  {
    type Iter<'a> = dedup::Iter<
      MapEntry<'a, K, V>,
      Rewinder<'a, K, V>,
      Ascend,
      NoopValidator,
      TombstoneValidator,
    >;
  }

  impl<K, V> Sealed<K, V> for MaybeTombstone
  where
    K: 'static,
    V: 'static,
  {
    type Iter<'a> =
      valid::Iter<MapEntry<'a, K, V>, Rewinder<'a, K, V>, Ascend, NoopValidator, NoopValidator>;
  }
}

pub struct Rewinder<'a, K, V>(&'a SkipMap<K, V>);

impl<'a, K, V> snapshotor::Rewindable for Rewinder<'a, K, V>
where
  K: Ord + 'static,
  V: 'static,
{
  type Entry = MapEntry<'a, K, V>;

  fn first(&self) -> Option<Self::Entry> {
    self.0.inner.front().map(MapEntry)
  }

  fn last(&self) -> Option<Self::Entry> {
    self.0.inner.back().map(MapEntry)
  }
}

/// a
pub struct Iter<'a, K, V, S>
where
  S: IterState<K, V>,
{
  iter: S::Iter<'a>,
  query_version: u64,
}

impl<'a, K, V> Iter<'a, K, V, Active>
where
  K: Ord + 'static,
  V: 'static,
{
  #[inline]
  pub(super) fn new(version: u64, map: &'a super::SkipMap<K, V>) -> Self {
    Self {
      iter: Builder::new(Rewinder(map))
        .with_value_validator(TombstoneValidator)
        .iter(version),
      query_version: version,
    }
  }
}

impl<'a, K, V> Iter<'a, K, V, MaybeTombstone>
where
  K: Ord + 'static,
  V: 'static,
{
  #[inline]
  pub(super) fn with_tombstone(version: u64, map: &'a super::SkipMap<K, V>) -> Self {
    Self {
      iter: Builder::new(Rewinder(map)).iter(version),
      query_version: version,
    }
  }
}

impl<'a, K, V, S> Iterator for Iter<'a, K, V, S>
where
  K: Ord + 'static,
  V: 'static,
  S: IterState<K, V>,
  S::Iter<'a>: Iterator<Item = MapEntry<'a, K, V>>,
{
  type Item = Entry<'a, K, V, S>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    self
      .iter
      .next()
      .map(|ent| Entry::new(ent, self.query_version))
  }
}

impl<'a, K, V, S> DoubleEndedIterator for Iter<'a, K, V, S>
where
  K: Ord + 'static,
  V: 'static,
  S: IterState<K, V>,
  S::Iter<'a>: DoubleEndedIterator<Item = MapEntry<'a, K, V>>,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    self
      .iter
      .next_back()
      .map(|ent| Entry::new(ent, self.query_version))
  }
}
