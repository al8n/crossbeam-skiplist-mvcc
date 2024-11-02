use core::ops::{Bound, RangeBounds, RangeToInclusive};

use crossbeam_skiplist::{
  map::{Iter as CIter, Range as CRange},
  Comparable,
};

use super::{CEntry, Entry, Values, VersionedEntry};

/// An iterator over the entries of a `SkipMap`.
pub struct Iter<'a, K, V> {
  iter: CIter<'a, K, Values<V>>,
  query_version: u64,
}

impl<'a, K, V> Iter<'a, K, V> {
  pub(super) fn new(iter: CIter<'a, K, Values<V>>, query_version: u64) -> Self {
    Self {
      iter,
      query_version,
    }
  }
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
where
  K: Ord,
{
  type Item = Entry<'a, K, V>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
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
  }
}

impl<K, V> DoubleEndedIterator for Iter<'_, K, V>
where
  K: Ord,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
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
  }
}

/// An iterator over a subset of entries of a `SkipMap`.
pub struct Range<'a, Q, R, K, V>
where
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
{
  range: CRange<'a, Q, R, K, Values<V>>,
  query_version: u64,
}

impl<'a, Q, R, K, V> Range<'a, Q, R, K, V>
where
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
{
  pub(super) fn new(range: CRange<'a, Q, R, K, Values<V>>, query_version: u64) -> Self {
    Self {
      range,
      query_version,
    }
  }
}

impl<'a, Q, R, K, V> Iterator for Range<'a, Q, R, K, V>
where
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
  K: Ord,
{
  type Item = Entry<'a, K, V>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
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
  }
}

impl<Q, R, K, V> DoubleEndedIterator for Range<'_, Q, R, K, V>
where
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
  K: Ord,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
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
  }
}

struct Latest<'a, K, V> {
  values_iter: CRange<'a, u64, RangeToInclusive<u64>, u64, Option<V>>,
  ent: CEntry<'a, K, Values<V>>,
}

/// An iterator over the entries with all versions of a `SkipMap`.
pub struct IterAll<'a, K, V> {
  iter: CIter<'a, K, Values<V>>,
  latest: Option<Latest<'a, K, V>>,
  query_version: u64,
}

impl<'a, K, V> IterAll<'a, K, V> {
  pub(super) fn new(iter: CIter<'a, K, Values<V>>, query_version: u64) -> Self {
    Self {
      latest: None,
      iter,
      query_version,
    }
  }
}

impl<'a, K, V> Iterator for IterAll<'a, K, V>
where
  K: Ord,
{
  type Item = VersionedEntry<'a, K, V>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
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
            return Some(VersionedEntry::new(
              latest.ent.clone(),
              value,
              self.query_version,
            ));
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

impl<K, V> DoubleEndedIterator for IterAll<'_, K, V>
where
  K: Ord,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
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
            return Some(VersionedEntry::new(
              latest.ent.clone(),
              value,
              self.query_version,
            ));
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

/// An iterator over the entries with all versions of a `SkipMap`.
pub struct RangeAll<'a, Q, R, K, V>
where
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
{
  iter: CRange<'a, Q, R, K, Values<V>>,
  latest: Option<Latest<'a, K, V>>,
  query_version: u64,
}

impl<'a, Q, R, K, V> RangeAll<'a, Q, R, K, V>
where
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
{
  pub(super) fn new(iter: CRange<'a, Q, R, K, Values<V>>, query_version: u64) -> Self {
    Self {
      latest: None,
      iter,
      query_version,
    }
  }
}

impl<'a, Q, R, K, V> Iterator for RangeAll<'a, Q, R, K, V>
where
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
  K: Ord,
{
  type Item = VersionedEntry<'a, K, V>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
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
            return Some(VersionedEntry::new(
              latest.ent.clone(),
              value,
              self.query_version,
            ));
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

impl<Q, R, K, V> DoubleEndedIterator for RangeAll<'_, Q, R, K, V>
where
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
  K: Ord,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
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
            return Some(VersionedEntry::new(
              latest.ent.clone(),
              value,
              self.query_version,
            ));
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
