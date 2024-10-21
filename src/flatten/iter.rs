use core::{
  cmp::Ordering,
  ops::{Bound, RangeBounds},
};

use crossbeam_skiplist::Comparable;

use super::{Entry, Query, SkipMap, VersionedEntry};

/// `ComparableRangeBounds` is implemented as an extention to `RangeBounds` to
/// allow for comparison of items with range bounds.
trait ComparableRangeBounds<Q: ?Sized>: RangeBounds<Q> {
  /// Returns `true` if `item` is contained in the range.
  fn compare_contains<K>(&self, item: &K) -> bool
  where
    Q: Comparable<K>,
    K: ?Sized,
  {
    (match self.start_bound() {
      Bound::Included(start) => start.compare(item) != Ordering::Greater,
      Bound::Excluded(start) => start.compare(item) == Ordering::Less,
      Bound::Unbounded => true,
    }) && (match self.end_bound() {
      Bound::Included(end) => end.compare(item) != Ordering::Less,
      Bound::Excluded(end) => end.compare(item) == Ordering::Greater,
      Bound::Unbounded => true,
    })
  }
}

impl<R, T> ComparableRangeBounds<T> for R
where
  R: ?Sized + RangeBounds<T>,
  T: ?Sized,
{
}

pub(super) struct BaseIter<'a, K, V, Q: ?Sized = K, R = core::ops::RangeFull> {
  pub(super) map: &'a SkipMap<K, V>,
  pub(super) version: u64,
  pub(super) range: Option<R>,
  pub(super) all_versions: bool,
  pub(super) head: Option<VersionedEntry<'a, K, V>>,
  pub(super) tail: Option<VersionedEntry<'a, K, V>>,
  pub(super) _phantom: core::marker::PhantomData<Q>,
}

impl<K, V, Q, R> Clone for BaseIter<'_, K, V, Q, R>
where
  Q: ?Sized,
  R: Clone,
{
  fn clone(&self) -> Self {
    Self {
      map: self.map,
      head: self.head.clone(),
      tail: self.tail.clone(),
      version: self.version,
      range: self.range.clone(),
      all_versions: self.all_versions,
      _phantom: core::marker::PhantomData,
    }
  }
}

impl<'a, K, V> BaseIter<'a, K, V> {
  fn new(version: u64, map: &'a SkipMap<K, V>, all_versions: bool) -> Self {
    Self {
      map,
      version,
      range: None,
      all_versions,
      head: None,
      tail: None,
      _phantom: core::marker::PhantomData,
    }
  }
}

impl<'a, K, V, Q, R> BaseIter<'a, K, V, Q, R>
where
  Q: ?Sized,
{
  fn range(version: u64, map: &'a SkipMap<K, V>, range: R, all_versions: bool) -> Self {
    Self {
      map,
      version,
      range: Some(range),
      all_versions,
      head: None,
      tail: None,
      _phantom: core::marker::PhantomData,
    }
  }
}

impl<K, V, Q, R> BaseIter<'_, K, V, Q, R>
where
  Q: ?Sized,
  R: RangeBounds<Q>,
{
  #[inline]
  fn check_bounds(&self, nk: &K) -> bool
  where
    Q: Comparable<K>,
  {
    if let Some(ref range) = self.range {
      range.compare_contains(nk)
    } else {
      true
    }
  }
}

impl<'a, K, V, Q, R> BaseIter<'a, K, V, Q, R>
where
  Q: ?Sized + Comparable<K>,
  R: RangeBounds<Q>,
  K: Ord,
{
  fn next_in(&mut self) -> Option<VersionedEntry<'a, K, V>> {
    let next_head = match self.head.as_ref() {
      Some(head) => head.ent.next(),
      None => self.map.inner.front(),
    };

    let next_head = if self.all_versions {
      SkipMap::find_next(next_head, self.version, |nk| self.check_bounds(nk))
    } else {
      SkipMap::find_next_max_version(next_head, self.version, |nk| {
        if let Some(ref head) = self.head {
          head.key().ne(nk) && self.check_bounds(nk)
        } else {
          self.check_bounds(nk)
        }
      })
    }
    .map(|ent| VersionedEntry::new(ent, self.version));

    match (next_head, &self.tail) {
      (Some(next), Some(t))
        if next
          .key()
          .cmp(t.key())
          .then_with(|| t.version().cmp(&next.version()))
          .is_ge() =>
      {
        self.head = Some(next);
        None
      }
      (Some(next), _) => {
        self.head = Some(next);
        self.head.clone()
      }
      (None, _) => {
        self.head = None;
        None
      }
    }
  }

  fn prev(&mut self) -> Option<VersionedEntry<'a, K, V>> {
    let next_tail = match self.tail.as_ref() {
      Some(tail) => tail.ent.prev(),
      None => self.map.inner.back(),
    };

    let next_tail = if self.all_versions {
      SkipMap::find_prev(next_tail, self.version, |nk| self.check_bounds(nk))
    } else {
      SkipMap::find_prev_max_version(next_tail, self.version, |nk| {
        if let Some(ref tail) = self.tail {
          tail.key().ne(nk) && self.check_bounds(nk)
        } else {
          self.check_bounds(nk)
        }
      })
    }
    .map(|ent| VersionedEntry::new(ent, self.version));

    match (&self.head, next_tail) {
      // The prev key is smaller than the latest head key we observed with this iterator.
      (Some(h), Some(next))
        if h
          .key()
          .cmp(next.key())
          .then_with(|| h.version().cmp(&next.version()))
          .is_ge() =>
      {
        self.tail = Some(next);
        None
      }
      (_, Some(next)) => {
        self.tail = Some(next);
        self.tail.clone()
      }
      (_, None) => {
        self.tail = None;
        None
      }
    }
  }

  fn range_next(&mut self) -> Option<VersionedEntry<'a, K, V>> {
    let next_head = match self.head.as_ref() {
      Some(head) => head.ent.next(),
      None => {
        let start_bound = self
          .range
          .as_ref()
          .unwrap()
          .start_bound()
          .map(|q| Query::new(self.version, q));
        self.map.inner.lower_bound(start_bound.as_ref())
      }
    };

    self.head = if self.all_versions {
      SkipMap::find_next(next_head, self.version, |nk| self.check_bounds(nk))
    } else {
      SkipMap::find_next_max_version(next_head, self.version, |nk| {
        if let Some(ref head) = self.head {
          head.key().ne(nk) && self.check_bounds(nk)
        } else {
          self.check_bounds(nk)
        }
      })
    }
    .map(|ent| VersionedEntry::new(ent, self.version));

    if let Some(ref h) = self.head {
      match &self.tail {
        Some(t) => {
          let bound = Bound::Excluded(t.key());
          if !below_upper_bound(&bound, h.key()) {
            self.head = None;
            self.tail = None;
          }
        }
        None => {
          let bound = self.range.as_ref().unwrap().end_bound();
          if !below_upper_bound_compare(&bound, h.key()) {
            self.head = None;
            self.tail = None;
          }
        }
      }
    }

    self.head.clone()
  }

  fn range_prev(&mut self) -> Option<VersionedEntry<'a, K, V>> {
    let next_tail = match self.tail.as_ref() {
      Some(tail) => tail.ent.prev(),
      None => {
        let end_bound = self
          .range
          .as_ref()
          .unwrap()
          .end_bound()
          .map(|q| Query::new(self.version, q));
        self.map.inner.upper_bound(end_bound.as_ref())
      }
    };

    self.tail = if self.all_versions {
      SkipMap::find_prev(next_tail, self.version, |nk| self.check_bounds(nk))
    } else {
      SkipMap::find_prev_max_version(next_tail, self.version, |nk| {
        if let Some(ref tail) = self.tail {
          tail.key().ne(nk) && self.check_bounds(nk)
        } else {
          self.check_bounds(nk)
        }
      })
    }
    .map(|ent| VersionedEntry::new(ent, self.version));

    if let Some(ref t) = self.tail {
      match &self.head {
        Some(h) => {
          let bound = Bound::Excluded(h.key());
          if !above_lower_bound(&bound, t.key()) {
            self.head = None;
            self.tail = None;
          }
        }
        None => {
          let bound = self.range.as_ref().unwrap().start_bound();
          if !above_lower_bound_compare(&bound, t.key()) {
            self.head = None;
            self.tail = None;
          }
        }
      }
    }

    self.tail.clone()
  }

  /// Moves the iterator to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// **Note:** This method will clear the current state of the iterator.
  pub(super) fn seek_upper_bound<QR>(
    &mut self,
    upper: Bound<&QR>,
  ) -> Option<VersionedEntry<'a, K, V>>
  where
    QR: ?Sized + Comparable<K>,
  {
    self.head = None;
    self.tail = None;

    match upper {
      Bound::Included(key) => self.seek_le(key).inspect(|ent| {
        self.head = Some(ent.clone());
      }),
      Bound::Excluded(key) => self.seek_lt(key).inspect(|ent| {
        self.head = Some(ent.clone());
      }),
      Bound::Unbounded => self.last(),
    }
  }

  /// Moves the iterator to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// **Note:** This method will clear the current state of the iterator.
  pub(super) fn seek_lower_bound<QR>(
    &mut self,
    lower: Bound<&QR>,
  ) -> Option<VersionedEntry<'a, K, V>>
  where
    QR: ?Sized + Comparable<K>,
  {
    self.head = None;
    self.tail = None;

    match lower {
      Bound::Included(key) => self.seek_ge(key).inspect(|ent| {
        self.head = Some(ent.clone());
      }),
      Bound::Excluded(key) => self.seek_gt(key).inspect(|ent| {
        self.head = Some(ent.clone());
      }),
      Bound::Unbounded => self.first(),
    }
  }

  /// Moves the iterator to the first entry whose key is greater than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_ge<QR>(&self, key: &QR) -> Option<VersionedEntry<'a, K, V>>
  where
    QR: ?Sized + Comparable<K>,
  {
    let q = Query::new(self.version, key);
    let n = self.map.inner.lower_bound(Bound::Included(&q)); // find the key with the max version.

    if self.all_versions {
      SkipMap::find_next(n, self.version, |nk| {
        if let Some(ref range) = self.range {
          range.compare_contains(nk)
        } else {
          true
        }
      })
    } else {
      SkipMap::find_next_max_version(n, self.version, |nk| {
        if let Some(ref range) = self.range {
          range.compare_contains(nk)
        } else {
          true
        }
      })
    }
    .map(|ent| VersionedEntry::new(ent, self.version))
  }

  /// Moves the iterator to the first entry whose key is greater than
  /// the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_gt<QR>(&self, key: &QR) -> Option<VersionedEntry<'a, K, V>>
  where
    QR: ?Sized + Comparable<K>,
  {
    let q = Query::new(0, key);
    let n = self.map.inner.lower_bound(Bound::Excluded(&q));

    if self.all_versions {
      SkipMap::find_next(n, self.version, |nk| {
        if let Some(ref range) = self.range {
          range.compare_contains(nk)
        } else {
          true
        }
      })
    } else {
      SkipMap::find_next_max_version(n, self.version, |nk| {
        if let Some(ref range) = self.range {
          range.compare_contains(nk)
        } else {
          true
        }
      })
    }
    .map(|ent| VersionedEntry::new(ent, self.version))
  }

  /// Moves the iterator to the first entry whose key is less than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_le<QR>(&self, key: &QR) -> Option<VersionedEntry<'a, K, V>>
  where
    QR: ?Sized + Comparable<K>,
  {
    let q = Query::new(0, key);
    let n = self.map.inner.upper_bound(Bound::Included(&q));

    if self.all_versions {
      SkipMap::find_prev(n, self.version, |nk| {
        if let Some(ref range) = self.range {
          range.compare_contains(nk)
        } else {
          true
        }
      })
    } else {
      SkipMap::find_prev_max_version(n, self.version, |nk| {
        if let Some(ref range) = self.range {
          range.compare_contains(nk)
        } else {
          true
        }
      })
    }
    .map(|ent| VersionedEntry::new(ent, self.version))
  }

  /// Moves the iterator to the last entry whose key is less than the given
  /// key. Returns the key and value if the iterator is pointing at a valid entry,
  /// and `None` otherwise.
  fn seek_lt<QR>(&self, key: &QR) -> Option<VersionedEntry<'a, K, V>>
  where
    QR: ?Sized + Comparable<K>,
  {
    let q = Query::new(self.version, key);
    let n = self.map.inner.upper_bound(Bound::Excluded(&q));

    if self.all_versions {
      SkipMap::find_prev(n, self.version, |nk| {
        if let Some(ref range) = self.range {
          range.compare_contains(nk)
        } else {
          true
        }
      })
    } else {
      SkipMap::find_prev_max_version(n, self.version, |nk| self.check_bounds(nk))
    }
    .map(|ent| VersionedEntry::new(ent, self.version))
  }

  #[inline]
  fn first(&mut self) -> Option<VersionedEntry<'a, K, V>> {
    self.head = None;
    self.tail = None;
    self.next()
  }

  #[inline]
  fn last(&mut self) -> Option<VersionedEntry<'a, K, V>> {
    self.tail = None;
    self.head = None;
    self.prev()
  }
}

impl<'a, K, V, Q, R> Iterator for BaseIter<'a, K, V, Q, R>
where
  Q: ?Sized + Comparable<K>,
  R: RangeBounds<Q>,
  K: Ord,
{
  type Item = VersionedEntry<'a, K, V>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    if self.range.is_none() {
      self.next_in()
    } else {
      self.range_next()
    }
  }
}

impl<K, V, Q, R> DoubleEndedIterator for BaseIter<'_, K, V, Q, R>
where
  Q: ?Sized + Comparable<K>,
  R: RangeBounds<Q>,
  K: Ord,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    if self.range.is_none() {
      self.prev()
    } else {
      self.range_prev()
    }
  }
}

/// An iterator over the entries of a `SkipMap`.
pub struct Iter<'a, K, V>(pub(super) BaseIter<'a, K, V>);

impl<K, V> Clone for Iter<'_, K, V> {
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, K, V> Iter<'a, K, V> {
  #[inline]
  pub(super) fn new(map: &'a SkipMap<K, V>, query_version: u64) -> Self {
    Self(BaseIter::new(query_version, map, false))
  }
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
where
  K: Ord,
{
  type Item = Entry<'a, K, V>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    self.0.next().map(Entry)
  }
}

impl<K, V> DoubleEndedIterator for Iter<'_, K, V>
where
  K: Ord,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    self.0.next_back().map(Entry)
  }
}

/// An iterator over the entries with all versions of a `SkipMap`.
pub struct AllVersionsIter<'a, K, V>(pub(super) BaseIter<'a, K, V>);

impl<K, V> Clone for AllVersionsIter<'_, K, V> {
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, K, V> AllVersionsIter<'a, K, V> {
  #[inline]
  pub(super) fn new(map: &'a SkipMap<K, V>, query_version: u64) -> Self {
    Self(BaseIter::new(query_version, map, true))
  }
}

impl<'a, K, V> Iterator for AllVersionsIter<'a, K, V>
where
  K: Ord,
{
  type Item = VersionedEntry<'a, K, V>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    self.0.next()
  }
}

impl<K, V> DoubleEndedIterator for AllVersionsIter<'_, K, V>
where
  K: Ord,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    self.0.next_back()
  }
}

/// An iterator over a subset of entries of a `SkipMap`.
pub struct Range<'a, Q, R, K, V>(pub(super) BaseIter<'a, K, V, Q, R>)
where
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>;

impl<'a, Q, R, K, V> Range<'a, Q, R, K, V>
where
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
{
  pub(super) fn new(range: R, map: &'a SkipMap<K, V>, query_version: u64) -> Self {
    Self(BaseIter::range(query_version, map, range, false))
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
    self.0.next().map(Entry)
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
    self.0.next_back().map(Entry)
  }
}

/// An iterator over the entries with all versions of a `SkipMap`.
pub struct AllVersionsRange<'a, Q, R, K, V>(pub(super) BaseIter<'a, K, V, Q, R>)
where
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>;

impl<'a, Q, R, K, V> AllVersionsRange<'a, Q, R, K, V>
where
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
{
  pub(super) fn new(range: R, map: &'a SkipMap<K, V>, query_version: u64) -> Self {
    Self(BaseIter::range(query_version, map, range, true))
  }
}

impl<'a, Q, R, K, V> Iterator for AllVersionsRange<'a, Q, R, K, V>
where
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
  K: Ord,
{
  type Item = VersionedEntry<'a, K, V>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    self.0.next()
  }
}

impl<Q, R, K, V> DoubleEndedIterator for AllVersionsRange<'_, Q, R, K, V>
where
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
  K: Ord,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    self.0.next_back()
  }
}

/// Helper function to check if a value is above a lower bound
fn above_lower_bound_compare<V, T: ?Sized + Comparable<V>>(bound: &Bound<&T>, other: &V) -> bool {
  match *bound {
    Bound::Unbounded => true,
    Bound::Included(key) => key.compare(other).is_le(),
    Bound::Excluded(key) => key.compare(other).is_lt(),
  }
}

/// Helper function to check if a value is above a lower bound
fn above_lower_bound<K: ?Sized + Ord>(bound: &Bound<&K>, other: &K) -> bool {
  match *bound {
    Bound::Unbounded => true,
    Bound::Included(key) => key.cmp(other).is_le(),
    Bound::Excluded(key) => key.cmp(other).is_lt(),
  }
}

/// Helper function to check if a value is below an upper bound
fn below_upper_bound_compare<V: ?Sized, T: ?Sized + Comparable<V>>(
  bound: &Bound<&T>,
  other: &V,
) -> bool {
  match *bound {
    Bound::Unbounded => true,
    Bound::Included(key) => key.compare(other).is_ge(),
    Bound::Excluded(key) => key.compare(other).is_gt(),
  }
}

/// Helper function to check if a value is below an upper bound
fn below_upper_bound<K: ?Sized + Ord>(bound: &Bound<&K>, other: &K) -> bool {
  match *bound {
    Bound::Unbounded => true,
    Bound::Included(key) => key.cmp(other).is_ge(),
    Bound::Excluded(key) => key.cmp(other).is_gt(),
  }
}
