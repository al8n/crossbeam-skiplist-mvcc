use core::ops::{Bound, RangeBounds, RangeToInclusive};
use std::marker::PhantomData;

use crossbeam_skiplist::{
  equivalentor::{Comparator, QueryComparator},
  map::{Iter as CIter, Range as CRange},
  Ascend,
};
use dbutils::state::State;

use super::{CEntry, Entry, Values};

struct Latest<'a, K, V, C> {
  values_iter: CRange<'a, u64, RangeToInclusive<u64>, u64, Option<V>, Ascend>,
  ent: CEntry<'a, K, Values<V>, C>,
}

/// An iterator over the entries of a `SkipMap`.
pub struct Iter<'a, K, V, S, C> {
  iter: CIter<'a, K, Values<V>, C>,
  query_version: u64,
  latest: Option<Latest<'a, K, V, C>>,
  _s: PhantomData<S>,
}

impl<'a, K, V, S, C> Iter<'a, K, V, S, C>
where
  S: State,
{
  pub(super) fn new(iter: CIter<'a, K, Values<V>, C>, query_version: u64) -> Self {
    Self {
      iter,
      query_version,
      latest: None,
      _s: PhantomData,
    }
  }
}

impl<'a, K, V, S, C> Iterator for Iter<'a, K, V, S, C>
where
  C: Comparator<K>,
  S: State,
{
  type Item = Entry<'a, K, V, S, C>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    if S::ALWAYS_VALID {
      loop {
        let entry = self.iter.next()?;

        let value = entry
          .value()
          .upper_bound(Bound::Included(&self.query_version));
        if let Some(value) = value {
          if value.value().is_some() {
            return Some(Entry::new(entry, value, self.query_version));
          }
        }
      }
    } else {
      loop {
        match self.latest {
          Some(ref mut latest) => match latest.values_iter.next_back() {
            None => {
              let ent = self.iter.next()?;
              let values_iter = ent.value().range(..=self.query_version);
              latest.values_iter = values_iter;
              latest.ent = ent;
            }
            Some(value) => {
              return Some(Entry::new(latest.ent.clone(), value, self.query_version));
            }
          },
          None => {
            let ent = self.iter.next()?;
            let values_iter = ent.value().range(..=self.query_version);
            let latest = Latest { values_iter, ent };
            self.latest = Some(latest);
          }
        }
      }
    }
  }
}

impl<K, V, S, C> DoubleEndedIterator for Iter<'_, K, V, S, C>
where
  C: Comparator<K>,
  S: State,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    if S::ALWAYS_VALID {
      loop {
        let entry = self.iter.next_back()?;

        let value = entry
          .value()
          .upper_bound(Bound::Included(&self.query_version));
        if let Some(value) = value {
          if value.value().is_some() {
            return Some(Entry::new(entry, value, self.query_version));
          }
        }
      }
    } else {
      loop {
        match self.latest {
          Some(ref mut latest) => match latest.values_iter.next() {
            None => {
              let ent = self.iter.next_back()?;
              let values_iter = ent.value().range(..=self.query_version);
              latest.values_iter = values_iter;
              latest.ent = ent;
            }
            Some(value) => {
              return Some(Entry::new(latest.ent.clone(), value, self.query_version));
            }
          },
          None => {
            let ent = self.iter.next_back()?;
            let values_iter = ent.value().range(..=self.query_version);
            let latest = Latest { values_iter, ent };
            self.latest = Some(latest);
          }
        }
      }
    }
  }
}

/// An iterator over a subset of entries of a `SkipMap`.
pub struct Range<'a, K, V, S, Q, R, C>
where
  R: RangeBounds<Q>,
  Q: ?Sized,
{
  range: CRange<'a, Q, R, K, Values<V>, C>,
  latest: Option<Latest<'a, K, V, C>>,
  query_version: u64,
  _s: PhantomData<S>,
}

impl<'a, K, V, S, Q, R, C> Range<'a, K, V, S, Q, R, C>
where
  R: RangeBounds<Q>,
  Q: ?Sized,
{
  pub(super) fn new(range: CRange<'a, Q, R, K, Values<V>, C>, query_version: u64) -> Self {
    Self {
      range,
      query_version,
      latest: None,
      _s: PhantomData,
    }
  }
}

impl<'a, K, V, S, Q, R, C> Iterator for Range<'a, K, V, S, Q, R, C>
where
  R: RangeBounds<Q>,
  Q: ?Sized,
  S: State,
  C: QueryComparator<K, Q>,
{
  type Item = Entry<'a, K, V, S, C>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    if S::ALWAYS_VALID {
      loop {
        let entry = self.range.next()?;

        let value = entry
          .value()
          .upper_bound(Bound::Included(&self.query_version));
        if let Some(value) = value {
          if value.value().is_some() {
            return Some(Entry::new(entry, value, self.query_version));
          }
        }
      }
    } else {
      loop {
        match self.latest {
          Some(ref mut latest) => match latest.values_iter.next_back() {
            None => {
              let ent = self.range.next()?;
              let values_iter = ent.value().range(..=self.query_version);
              latest.values_iter = values_iter;
              latest.ent = ent;
            }
            Some(value) => {
              return Some(Entry::new(latest.ent.clone(), value, self.query_version));
            }
          },
          None => {
            let ent = self.range.next()?;
            let values_iter = ent.value().range(..=self.query_version);
            let latest = Latest { values_iter, ent };
            self.latest = Some(latest);
          }
        }
      }
    }
  }
}

impl<K, V, S, Q, R, C> DoubleEndedIterator for Range<'_, K, V, S, Q, R, C>
where
  R: RangeBounds<Q>,
  Q: ?Sized,
  S: State,
  C: QueryComparator<K, Q>,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    if S::ALWAYS_VALID {
      loop {
        let entry = self.range.next_back()?;

        let value = entry
          .value()
          .upper_bound(Bound::Included(&self.query_version));
        if let Some(value) = value {
          if value.value().is_some() {
            return Some(Entry::new(entry, value, self.query_version));
          }
        }
      }
    } else {
      loop {
        match self.latest {
          Some(ref mut latest) => match latest.values_iter.next() {
            None => {
              let ent = self.range.next_back()?;
              let values_iter = ent.value().range(..=self.query_version);
              latest.values_iter = values_iter;
              latest.ent = ent;
            }
            Some(value) => {
              return Some(Entry::new(latest.ent.clone(), value, self.query_version));
            }
          },
          None => {
            let ent = self.range.next_back()?;
            let values_iter = ent.value().range(..=self.query_version);
            let latest = Latest { values_iter, ent };
            self.latest = Some(latest);
          }
        }
      }
    }
  }
}
