use std::ops::{Bound, RangeBounds};

use crossbeam_skiplist::equivalentor::QueryComparator;
use dbutils::state::{Active, MaybeTombstone, State};
use snapshotor::{dedup, valid, Builder, NoopValidator, Seekable};

use crate::sealed::TombstoneValidator;

use super::{entry::MapEntry, Entry, Query};

/// The state of the range.
pub trait RangeState<K, V>: sealed::Sealed<K, V> {}

impl<K, V, T> RangeState<K, V> for T where T: sealed::Sealed<K, V> {}

mod sealed {
  use super::*;

  pub trait Sealed<K, V>: State {
    type Range<'a, Q, R, C>
    where
      Q: ?Sized,
      R: RangeBounds<Q>,
      C: QueryComparator<K, Q> + 'static;
  }

  impl<K, V> Sealed<K, V> for Active
  where
    K: 'static,
    V: 'static,
  {
    type Range<'a, Q, R, C>
      = dedup::RefRange<
      'a,
      R,
      Q,
      Seeker<'a, K, V, C>,
      MapEntry<'a, K, V, C>,
      C,
      NoopValidator,
      TombstoneValidator,
    >
    where
      Q: ?Sized,
      R: RangeBounds<Q>,
      C: QueryComparator<K, Q> + 'static;
  }

  impl<K, V> Sealed<K, V> for MaybeTombstone
  where
    K: 'static,
    V: 'static,
  {
    type Range<'a, Q, R, C>
      = valid::RefRange<
      'a,
      R,
      Q,
      Seeker<'a, K, V, C>,
      MapEntry<'a, K, V, C>,
      C,
      NoopValidator,
      NoopValidator,
    >
    where
      Q: ?Sized,
      R: RangeBounds<Q>,
      C: QueryComparator<K, Q> + 'static;
  }
}

pub struct Seeker<'a, K, V, C> {
  map: &'a super::SkipMap<K, V, C>,
  query_version: u64,
}

impl<'a, K, V, Q, C> Seekable<Q> for Seeker<'a, K, V, C>
where
  V: 'static,
  Q: ?Sized,
  C: QueryComparator<K, Q>,
{
  type Entry = MapEntry<'a, K, V, C>;

  fn lower_bound(&self, bound: Bound<&Q>) -> Option<Self::Entry> {
    self
      .map
      .inner
      .lower_bound(bound.map(|q| Query::new(self.query_version, q)).as_ref())
      .map(MapEntry)
  }

  fn upper_bound(&self, bound: Bound<&Q>) -> Option<Self::Entry> {
    self
      .map
      .inner
      .upper_bound(bound.map(|q| Query::new(0, q)).as_ref())
      .map(MapEntry)
  }
}

/// a
pub struct Range<'a, K, V, S, Q, R, C>
where
  C: QueryComparator<K, Q> + 'static,
  V: 'static,
  R: RangeBounds<Q>,
  Q: ?Sized,
  S: RangeState<K, V>,
{
  iter: S::Range<'a, Q, R, C>,
  version: u64,
}

impl<'a, K, V, Q, R, C> Range<'a, K, V, Active, Q, R, C>
where
  C: QueryComparator<K, Q> + 'static,
  K: 'static,
  V: 'static,
  R: RangeBounds<Q>,
  Q: ?Sized,
{
  #[inline]
  pub(super) fn new(version: u64, map: &'a super::SkipMap<K, V, C>, range: R) -> Self {
    let seeker = Seeker {
      map,
      query_version: version,
    };

    Self {
      iter: Builder::new(seeker)
        .with_value_validator(TombstoneValidator)
        .with_comparator(&map.inner.comparator().0)
        .range(version, range),
      version,
    }
  }
}

impl<'a, K, V, Q, R, C> Range<'a, K, V, MaybeTombstone, Q, R, C>
where
  C: QueryComparator<K, Q> + 'static,
  K: 'static,
  V: 'static,
  R: RangeBounds<Q>,
  Q: ?Sized,
{
  #[inline]
  pub(super) fn with_tombstone(version: u64, map: &'a super::SkipMap<K, V, C>, range: R) -> Self {
    let seeker = Seeker {
      map,
      query_version: version,
    };

    Self {
      iter: Builder::new(seeker)
        .with_comparator(&map.inner.comparator().0)
        .range(version, range),
      version,
    }
  }
}

impl<'a, K, V, S, Q, R, C> Iterator for Range<'a, K, V, S, Q, R, C>
where
  C: QueryComparator<K, Q> + 'static,
  K: 'static,
  V: 'static,
  R: RangeBounds<Q>,
  Q: ?Sized,
  S: RangeState<K, V>,
  S::Range<'a, Q, R, C>: Iterator<Item = MapEntry<'a, K, V, C>>,
{
  type Item = Entry<'a, K, V, S, C>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    self.iter.next().map(|ent| Entry::new(ent, self.version))
  }
}

impl<'a, K, V, S, Q, R, C> DoubleEndedIterator for Range<'a, K, V, S, Q, R, C>
where
  C: QueryComparator<K, Q> + 'static,
  K: 'static,
  V: 'static,
  Q: ?Sized,
  R: RangeBounds<Q>,
  S: RangeState<K, V>,
  S::Range<'a, Q, R, C>: DoubleEndedIterator<Item = MapEntry<'a, K, V, C>>,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    self
      .iter
      .next_back()
      .map(|ent| Entry::new(ent, self.version))
  }
}
