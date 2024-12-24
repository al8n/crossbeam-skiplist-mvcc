use crossbeam_skiplist::equivalentor::Comparator;
use dbutils::state::{Active, MaybeTombstone, State};
use snapshotor::{dedup, valid, Builder, NoopValidator};

use crate::sealed::TombstoneValidator;

use super::{entry::MapEntry, Entry, SkipMap};

/// The state of the iterator.
pub trait IterState<K, V>: sealed::Sealed<K, V> {}

impl<K, V, T> IterState<K, V> for T where T: sealed::Sealed<K, V> {}

mod sealed {
  use super::*;

  pub trait Sealed<K, V>: State {
    type Iter<'a, C>
    where
      C: 'static;
  }

  impl<K, V> Sealed<K, V> for Active
  where
    K: 'static,
    V: 'static,
  {
    type Iter<'a, C>
      = dedup::RefIter<
      'a,
      MapEntry<'a, K, V, C>,
      Rewinder<'a, K, V, C>,
      C,
      NoopValidator,
      TombstoneValidator,
    >
    where
      C: 'static;
  }

  impl<K, V> Sealed<K, V> for MaybeTombstone
  where
    K: 'static,
    V: 'static,
  {
    type Iter<'a, C>
      = valid::RefIter<
      'a,
      MapEntry<'a, K, V, C>,
      Rewinder<'a, K, V, C>,
      C,
      NoopValidator,
      NoopValidator,
    >
    where
      C: 'static;
  }
}

pub struct Rewinder<'a, K, V, C>(&'a SkipMap<K, V, C>);

impl<'a, K, V, C> snapshotor::Rewindable for Rewinder<'a, K, V, C>
where
  C: Comparator<K>,
{
  type Entry = MapEntry<'a, K, V, C>;

  fn first(&self) -> Option<Self::Entry> {
    self.0.inner.front().map(MapEntry)
  }

  fn last(&self) -> Option<Self::Entry> {
    self.0.inner.back().map(MapEntry)
  }
}

/// a
pub struct Iter<'a, K, V, S, C>
where
  S: IterState<K, V>,
  C: 'static,
{
  iter: S::Iter<'a, C>,
  query_version: u64,
}

impl<'a, K, V, C> Iter<'a, K, V, Active, C>
where
  K: 'static,
  V: 'static,
  C: Comparator<K> + 'static,
{
  #[inline]
  pub(super) fn new(version: u64, map: &'a super::SkipMap<K, V, C>) -> Self {
    Self {
      iter: Builder::new(Rewinder(map))
        .with_value_validator(TombstoneValidator)
        .with_comparator(&map.inner.comparator().0)
        .iter(version),
      query_version: version,
    }
  }
}

impl<'a, K, V, C> Iter<'a, K, V, MaybeTombstone, C>
where
  K: 'static,
  V: 'static,
  C: Comparator<K> + 'static,
{
  #[inline]
  pub(super) fn with_tombstone(version: u64, map: &'a super::SkipMap<K, V, C>) -> Self {
    Self {
      iter: Builder::new(Rewinder(map))
        .with_comparator(&map.inner.comparator().0)
        .iter(version),
      query_version: version,
    }
  }
}

impl<'a, K, V, S, C> Iterator for Iter<'a, K, V, S, C>
where
  K: 'static,
  V: 'static,
  S: IterState<K, V>,
  S::Iter<'a, C>: Iterator<Item = MapEntry<'a, K, V, C>>,
  C: Comparator<K> + 'static,
{
  type Item = Entry<'a, K, V, S, C>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    self
      .iter
      .next()
      .map(|ent| Entry::new(ent, self.query_version))
  }
}

impl<'a, K, V, S, C> DoubleEndedIterator for Iter<'a, K, V, S, C>
where
  K: 'static,
  V: 'static,
  S: IterState<K, V>,
  S::Iter<'a, C>: DoubleEndedIterator<Item = MapEntry<'a, K, V, C>>,
  C: Comparator<K> + 'static,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    self
      .iter
      .next_back()
      .map(|ent| Entry::new(ent, self.query_version))
  }
}
