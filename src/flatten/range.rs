use std::ops::{Bound, RangeBounds};

use dbutils::{
  equivalent::Comparable,
  equivalentor::Ascend,
  state::{Active, MaybeTombstone, State},
};
use snapshotor::{dedup, valid, Builder, NoopValidator, Seekable};

use crate::sealed::TombstoneValidator;

use super::{entry::MapEntry, Entry, Query};

/// The state of the range.
pub trait RangeState<K, V>: sealed::Sealed<K, V> {}

impl<K, V, T> RangeState<K, V> for T where T: sealed::Sealed<K, V> {}

mod sealed {
  use super::*;

  pub trait Sealed<K, V>: State {
    type Range<'a, Q, R>
    where
      K: Ord + Comparable<Q>,
      Q: ?Sized,
      R: RangeBounds<Q>;
  }

  impl<K, V> Sealed<K, V> for Active
  where
    K: 'static,
    V: 'static,
  {
    type Range<'a, Q, R>
      = dedup::Range<
      R,
      Q,
      Seeker<'a, K, V>,
      MapEntry<'a, K, V>,
      Ascend,
      NoopValidator,
      TombstoneValidator,
    >
    where
      K: Ord + Comparable<Q>,
      Q: ?Sized,
      R: RangeBounds<Q>;
  }

  impl<K, V> Sealed<K, V> for MaybeTombstone
  where
    K: 'static,
    V: 'static,
  {
    type Range<'a, Q, R>
      =
      valid::Range<R, Q, Seeker<'a, K, V>, MapEntry<'a, K, V>, Ascend, NoopValidator, NoopValidator>
    where
      K: Ord + Comparable<Q>,
      Q: ?Sized,
      R: RangeBounds<Q>;
  }
}

pub struct Seeker<'a, K, V> {
  map: &'a super::SkipMap<K, V>,
  query_version: u64,
}

impl<'a, K, V, Q> Seekable<Q> for Seeker<'a, K, V>
where
  K: Ord + Comparable<Q> + 'static,
  V: 'static,
  Q: ?Sized,
{
  type Entry = MapEntry<'a, K, V>;

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
pub struct Range<'a, K, V, S, Q, R>
where
  K: Ord + Comparable<Q> + 'static,
  V: 'static,
  R: RangeBounds<Q>,
  Q: ?Sized,
  S: RangeState<K, V>,
{
  iter: S::Range<'a, Q, R>,
  version: u64,
}

impl<'a, K, V, Q, R> Range<'a, K, V, Active, Q, R>
where
  K: Ord + Comparable<Q> + 'static,
  V: 'static,
  R: RangeBounds<Q>,
  Q: ?Sized,
{
  #[inline]
  pub(super) fn new(version: u64, map: &'a super::SkipMap<K, V>, range: R) -> Self {
    let seeker = Seeker {
      map,
      query_version: version,
    };

    Self {
      iter: Builder::new(seeker)
        .with_value_validator(TombstoneValidator)
        .range(version, range),
      version,
    }
  }
}

impl<'a, K, V, Q, R> Range<'a, K, V, MaybeTombstone, Q, R>
where
  K: Ord + Comparable<Q> + 'static,
  V: 'static,
  R: RangeBounds<Q>,
  Q: ?Sized,
{
  #[inline]
  pub(super) fn with_tombstone(version: u64, map: &'a super::SkipMap<K, V>, range: R) -> Self {
    let seeker = Seeker {
      map,
      query_version: version,
    };

    Self {
      iter: Builder::new(seeker).range(version, range),
      version,
    }
  }
}

impl<'a, K, V, S, Q, R> Iterator for Range<'a, K, V, S, Q, R>
where
  K: Ord + Comparable<Q> + 'static,
  V: 'static,
  R: RangeBounds<Q>,
  Q: ?Sized,
  S: RangeState<K, V>,
  S::Range<'a, Q, R>: Iterator<Item = MapEntry<'a, K, V>>,
{
  type Item = Entry<'a, K, V, S>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    self.iter.next().map(|ent| Entry::new(ent, self.version))
  }
}

impl<'a, K, V, S, Q, R> DoubleEndedIterator for Range<'a, K, V, S, Q, R>
where
  K: Ord + Comparable<Q> + 'static,
  V: 'static,
  Q: ?Sized,
  R: RangeBounds<Q>,
  S: RangeState<K, V>,
  S::Range<'a, Q, R>: DoubleEndedIterator<Item = MapEntry<'a, K, V>>,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    self
      .iter
      .next_back()
      .map(|ent| Entry::new(ent, self.version))
  }
}
