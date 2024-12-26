use core::{
  marker::PhantomData,
  ops::{Bound, RangeBounds},
  sync::atomic::{AtomicU64, Ordering},
};

use comparator::MultipleVersionsComparator;
use crossbeam_skiplist::{equivalentor::*, SkipMap as CSkipMap};

use dbutils::state::{Active, MaybeTombstone};

use crate::error::Error;

#[cfg(test)]
mod tests;

mod entry;
pub use entry::Entry;

mod iter;
pub use iter::Iter;
mod range;
pub use range::Range;

mod comparator;

struct Key<K> {
  key: K,
  version: u64,
}

impl<K> Key<K> {
  #[inline]
  const fn new(key: K, version: u64) -> Self {
    Self { key, version }
  }
}

struct Query<'a, Q: ?Sized, K: ?Sized> {
  _m: PhantomData<K>,
  query: &'a Q,
  version: u64,
}

impl<'a, Q: ?Sized, K: ?Sized> Query<'a, Q, K> {
  #[inline]
  fn new(version: u64, query: &'a Q) -> Self {
    Self {
      _m: PhantomData,
      query,
      version,
    }
  }
}

/// A multiple version ordered map based on a lock-free skip list.
///
/// For the difference between `nested::SkipMap` and `flatten::SkipMap`, see the [crate-level documentation](crate).
pub struct SkipMap<K, V, C = Ascend> {
  inner: CSkipMap<Key<K>, Option<V>, MultipleVersionsComparator<C>>,
  min_version: AtomicU64,
  max_version: AtomicU64,
  last_discard_version: AtomicU64,
}

impl<K, V, C: Default> Default for SkipMap<K, V, C> {
  #[inline]
  fn default() -> Self {
    Self::with_comparator(C::default())
  }
}

impl<K, V> SkipMap<K, V> {
  /// Returns a new, empty map.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  ///
  /// let map: SkipMap<i32, i32> = SkipMap::new();
  /// ```
  pub fn new() -> Self {
    Self {
      inner: CSkipMap::with_comparator(Ascend.into()),
      min_version: AtomicU64::new(u64::MAX),
      max_version: AtomicU64::new(0),
      last_discard_version: AtomicU64::new(0),
    }
  }
}

impl<K, V, C> SkipMap<K, V, C> {
  /// Returns a new, empty map.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::{flatten::SkipMap, Ascend};
  ///
  /// let map: SkipMap<i32, i32> = SkipMap::with_comparator(Ascend);
  /// ```
  pub fn with_comparator(cmp: C) -> Self {
    Self {
      inner: CSkipMap::with_comparator(cmp.into()),
      min_version: AtomicU64::new(u64::MAX),
      max_version: AtomicU64::new(0),
      last_discard_version: AtomicU64::new(0),
    }
  }

  /// Returns a reference to the map's comparator.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::{flatten::SkipMap, Ascend};
  ///
  /// let map: SkipMap<i32, i32> = SkipMap::with_comparator(Ascend);
  ///
  /// assert_eq!(map.comparator(), &Ascend);
  /// ```
  pub fn comparator(&self) -> &C {
    &self.inner.comparator().0
  }

  /// Returns `true` if the map may contain a value for the specified version.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  ///
  /// let map: SkipMap<i32, i32> = SkipMap::new();
  ///
  /// assert!(!map.may_contain_version(0));
  /// ```
  #[inline]
  pub fn may_contain_version(&self, version: u64) -> bool {
    version >= self.min_version.load(Ordering::Acquire)
  }

  /// Returns the minimum version in the map.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  ///
  /// let map: SkipMap<i32, i32> = SkipMap::new();
  ///
  /// // For an empty map, the minimum version is u64::MAX.
  /// assert_eq!(map.minimum_version(), u64::MAX);
  ///
  /// map.insert(0, 1, 1);
  ///
  /// assert_eq!(map.minimum_version(), 0);
  /// ```
  #[inline]
  pub fn minimum_version(&self) -> u64 {
    self.min_version.load(Ordering::Acquire)
  }

  /// Returns the maximum version in the map.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  ///
  /// let map: SkipMap<i32, i32> = SkipMap::new();
  ///
  /// // For an empty map, the maximum version is 0.
  /// assert_eq!(map.maximum_version(), 0);
  ///
  /// map.insert(1, 1, 1);
  ///
  /// assert_eq!(map.maximum_version(), 1);
  /// ```
  #[inline]
  pub fn maximum_version(&self) -> u64 {
    self.max_version.load(Ordering::Acquire)
  }

  /// Returns the total number of entries in the map.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  ///
  /// let map: SkipMap<i32, i32> = SkipMap::new();
  ///
  /// assert_eq!(map.len(), 0);
  ///
  /// map.insert(0, 1, 1);
  ///
  /// assert_eq!(map.len(), 1);
  ///
  /// map.insert(1, 1, 2);
  /// assert_eq!(map.len(), 2);
  /// ```
  #[inline]
  pub fn len(&self) -> usize {
    self.inner.len()
  }

  /// Returns `true` if the map contains no elements.
  ///
  /// ## Example
  ///
  /// ```rust
  ///
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  ///
  /// let map: SkipMap<i32, i32> = SkipMap::new();
  ///
  /// assert!(map.is_empty());
  /// ```
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.inner.is_empty()
  }

  fn update_versions(&self, version: u64) {
    let _ = self
      .min_version
      .fetch_update(Ordering::Release, Ordering::Acquire, |min_version| {
        min_version.gt(&version).then_some(version)
      });
    let _ = self
      .max_version
      .fetch_update(Ordering::Release, Ordering::Acquire, |max_version| {
        max_version.lt(&version).then_some(version)
      });
  }
}

impl<K, V, C> SkipMap<K, V, C>
where
  K: 'static,
  V: 'static,
  C: 'static,
{
  /// Returns `true` if the map contains a value for the specified key.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  ///
  /// let ages = SkipMap::new();
  /// ages.insert(0, "Bill Gates", 64);
  ///
  /// assert!(ages.contains_key(0, &"Bill Gates"));
  /// assert!(!ages.contains_key(0, &"Steve Jobs"));
  /// ```
  #[inline]
  pub fn contains_key<Q>(&self, version: u64, key: &Q) -> bool
  where
    C: QueryComparator<K, Q>,
    Q: ?Sized,
  {
    if !self.may_contain_version(version) {
      return false;
    }

    match self
      .inner
      .lower_bound(Bound::Included(&Query::new(version, key)))
    {
      Some(entry) => {
        let k = entry.key();

        if !entry.comparator().0.query_equivalent(&k.key, key) {
          return false;
        }

        if entry.value().is_none() {
          return false;
        }

        true
      }
      None => false,
    }
  }

  /// Returns `true` if the map contains a value for the specified key even though this entry already been marked as removed.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  ///
  /// let ages = SkipMap::new();
  /// ages.insert(0, "Bill Gates", 64);
  /// ages.remove(1, "Bill Gates");
  ///
  /// assert!(ages.contains_key_with_tombstone(0, &"Bill Gates"));
  /// assert!(ages.contains_key_with_tombstone(1, &"Bill Gates"));
  /// assert!(!ages.contains_key_with_tombstone(1, &"Steve Jobs"));
  /// ```
  #[inline]
  pub fn contains_key_with_tombstone<Q>(&self, version: u64, key: &Q) -> bool
  where
    C: QueryComparator<K, Q>,
    Q: ?Sized,
  {
    if !self.may_contain_version(version) {
      return false;
    }

    match self
      .inner
      .lower_bound(Bound::Included(&Query::new(version, key)))
    {
      Some(entry) => {
        let k = entry.key();
        if !entry.comparator().0.query_equivalent(&k.key, key) {
          return false;
        }

        true
      }
      None => false,
    }
  }

  /// Returns an entry with the specified `key`.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  ///
  /// let numbers: SkipMap<&str, i32> = SkipMap::new();
  /// assert!(numbers.get(0, "six").is_none());
  ///
  /// numbers.insert(0, "six", 6);
  /// assert_eq!(*numbers.get(0, "six").unwrap().value(), 6);
  /// ```
  pub fn get<Q>(&self, version: u64, key: &Q) -> Option<Entry<'_, K, V, Active, C>>
  where
    C: QueryComparator<K, Q>,
    Q: ?Sized,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    match self
      .inner
      .lower_bound(Bound::Included(&Query::new(version, key)))
    {
      Some(entry) => {
        let k = entry.key();
        if !entry.comparator().0.query_equivalent(&k.key, key) {
          return None;
        }

        if entry.value().is_none() {
          return None;
        }

        Some(Entry::new(entry.into(), version))
      }
      None => None,
    }
  }

  /// Returns an entry with the specified `key` even though this entry already been marked as removed.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  ///
  /// let numbers: SkipMap<&str, i32> = SkipMap::new();
  /// assert!(numbers.get_with_tombstone(0, "six").is_none());
  ///
  /// numbers.insert(0, "six", 6);
  /// numbers.remove(1, "six");
  ///
  /// assert!(numbers.get(1, "six").is_none());
  /// assert!(numbers.get_with_tombstone(1, "six").unwrap().value().is_none());
  /// ```
  pub fn get_with_tombstone<Q>(
    &self,
    version: u64,
    key: &Q,
  ) -> Option<Entry<'_, K, V, MaybeTombstone, C>>
  where
    C: QueryComparator<K, Q>,
    Q: ?Sized,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    match self
      .inner
      .lower_bound(Bound::Included(&Query::new(version, key)))
    {
      Some(entry) => {
        let k = entry.key();
        if !entry.comparator().0.query_equivalent(&k.key, key) {
          return None;
        }

        Some(Entry::new(entry.into(), version))
      }
      None => None,
    }
  }

  /// Returns an `Entry` pointing to the lowest element whose key is above
  /// the given bound. If no such element is found then `None` is
  /// returned.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  /// use std::ops::Bound::*;
  ///
  /// let numbers = SkipMap::new();
  /// numbers.insert(0, 6, "six");
  /// numbers.insert(0, 7, "seven");
  /// numbers.insert(0, 12, "twelve");
  ///
  /// let greater_than_five = numbers.lower_bound(0, Excluded(&5)).unwrap();
  /// assert_eq!(*greater_than_five.value(), "six");
  ///
  /// let greater_than_six = numbers.lower_bound(0, Excluded(&6)).unwrap();
  /// assert_eq!(*greater_than_six.value(), "seven");
  ///
  /// let greater_than_thirteen = numbers.lower_bound(0, Excluded(&13));
  /// assert!(greater_than_thirteen.is_none());
  /// ```
  pub fn lower_bound<'a, Q>(
    &'a self,
    version: u64,
    bound: Bound<&'a Q>,
  ) -> Option<Entry<'a, K, V, Active, C>>
  where
    C: QueryComparator<K, Q>,
    Q: ?Sized,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.range(version, (bound, Bound::Unbounded)).next()
  }

  /// Returns an `Entry` pointing to the lowest element whose key is above
  /// the given bound. If no such element is found then `None` is
  /// returned.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  /// use std::ops::Bound::*;
  ///
  /// let numbers = SkipMap::new();
  /// numbers.insert(0, 6, "six");
  /// numbers.insert(0, 7, "seven");
  /// numbers.insert(0, 12, "twelve");
  ///
  /// let greater_than_five = numbers.lower_bound_with_tombstone(0, Excluded(&5)).unwrap();
  /// assert_eq!(*greater_than_five.value().unwrap(), "six");
  ///
  /// let greater_than_six = numbers.lower_bound_with_tombstone(0, Excluded(&6)).unwrap();
  /// assert_eq!(*greater_than_six.value().unwrap(), "seven");
  ///
  /// let greater_than_thirteen = numbers.lower_bound_with_tombstone(0, Excluded(&13));
  /// assert!(greater_than_thirteen.is_none());
  /// ```
  pub fn lower_bound_with_tombstone<'a, Q>(
    &'a self,
    version: u64,
    bound: Bound<&Q>,
  ) -> Option<Entry<'a, K, V, MaybeTombstone, C>>
  where
    C: QueryComparator<K, Q>,
    Q: ?Sized,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.range_all(version, (bound, Bound::Unbounded)).next()
  }

  /// Returns an `Entry` pointing to the highest element whose key is below
  /// the given bound. If no such element is found then `None` is
  /// returned.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  /// use std::ops::Bound::*;
  ///
  /// let numbers = SkipMap::new();
  /// numbers.insert(0, 6, "six");
  /// numbers.insert(0, 7, "seven");
  /// numbers.insert(0, 12, "twelve");
  ///
  /// let less_than_eight = numbers.upper_bound(0, Excluded(&8)).unwrap();
  /// assert_eq!(*less_than_eight.value(), "seven");
  ///
  /// let less_than_six = numbers.upper_bound(0, Excluded(&6));
  /// assert!(less_than_six.is_none());
  /// ```
  pub fn upper_bound<'a, Q>(
    &'a self,
    version: u64,
    bound: Bound<&Q>,
  ) -> Option<Entry<'a, K, V, Active, C>>
  where
    C: QueryComparator<K, Q>,
    Q: ?Sized,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.range(version, (Bound::Unbounded, bound)).next_back()
  }

  /// Returns an `Entry` pointing to the highest element whose key is below
  /// the given bound. If no such element is found then `None` is
  /// returned.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  /// use std::ops::Bound::*;
  ///
  /// let numbers = SkipMap::new();
  /// numbers.insert(0, 6, "six");
  /// numbers.insert(0, 7, "seven");
  /// numbers.insert(0, 12, "twelve");
  ///
  /// let less_than_eight = numbers.upper_bound_with_tombstone(0, Excluded(&8)).unwrap();
  /// assert_eq!(*less_than_eight.value().unwrap(), "seven");
  ///
  /// let less_than_six = numbers.upper_bound_with_tombstone(0, Excluded(&6));
  /// assert!(less_than_six.is_none());
  /// ```
  pub fn upper_bound_with_tombstone<'a, Q>(
    &'a self,
    version: u64,
    bound: Bound<&Q>,
  ) -> Option<Entry<'a, K, V, MaybeTombstone, C>>
  where
    C: QueryComparator<K, Q>,
    Q: ?Sized,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self
      .range_all(version, (Bound::Unbounded, bound))
      .next_back()
  }

  /// Returns the entry with the smallest key.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  ///
  /// let numbers = SkipMap::new();
  /// numbers.insert(1, 5, "five");
  /// assert_eq!(*numbers.front(1).unwrap().value(), "five");
  /// numbers.insert(1, 6, "six");
  /// assert_eq!(*numbers.front(1).unwrap().value(), "five");
  /// ```
  pub fn front(&self, version: u64) -> Option<Entry<'_, K, V, Active, C>>
  where
    C: Comparator<K>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.iter(version).next()
  }

  /// Returns the entry with the smallest key.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  ///
  /// let numbers = SkipMap::new();
  /// numbers.insert(1, 5, "five");
  /// assert_eq!(*numbers.front_with_tombstone(1).unwrap().value().unwrap(), "five");
  /// numbers.insert(1, 6, "six");
  /// assert_eq!(*numbers.front_with_tombstone(1).unwrap().value().unwrap(), "five");
  /// ```
  pub fn front_with_tombstone(&self, version: u64) -> Option<Entry<'_, K, V, MaybeTombstone, C>>
  where
    C: Comparator<K>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.iter_all(version).next()
  }

  /// Returns the entry with the largest key.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  ///
  /// let numbers = SkipMap::new();
  /// numbers.insert(1, 5, "five");
  /// assert_eq!(*numbers.back(1).unwrap().value(), "five");
  /// numbers.insert(1, 6, "six");
  /// assert_eq!(*numbers.back(1).unwrap().value(), "six");
  /// ```
  pub fn back(&self, version: u64) -> Option<Entry<'_, K, V, Active, C>>
  where
    C: Comparator<K>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.iter(version).next_back()
  }

  /// Returns the entry with the largest key.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  ///
  /// let numbers = SkipMap::new();
  /// numbers.insert(1, 5, "five");
  /// assert_eq!(*numbers.back_with_tombstone(1).unwrap().value().unwrap(), "five");
  /// numbers.insert(1, 6, "six");
  /// assert_eq!(*numbers.back_with_tombstone(1).unwrap().value().unwrap(), "six");
  /// ```
  pub fn back_with_tombstone(&self, version: u64) -> Option<Entry<'_, K, V, MaybeTombstone, C>>
  where
    C: Comparator<K>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.iter_all(version).next_back()
  }

  /// Returns an iterator over all entries in the map,
  /// sorted by key.
  ///
  /// This iterator returns [`Entry`]s which
  /// can be used to access keys and their associated values.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  ///
  /// let numbers = SkipMap::new();
  /// numbers.insert(1, 6, "six");
  /// numbers.insert(1, 7, "seven");
  /// numbers.insert(1, 12, "twelve");
  ///
  /// // Print then numbers from least to greatest
  /// for entry in numbers.iter(1) {
  ///   let number = entry.key();
  ///   let number_str = entry.value();
  ///   println!("{} is {}", number, number_str);
  /// }
  /// ```
  pub fn iter(&self, version: u64) -> Iter<'_, K, V, Active, C>
  where
    C: Comparator<K>,
  {
    Iter::new(version, self)
  }

  /// Returns an iterator over all entries (all versions) in the map.
  pub fn iter_all(&self, version: u64) -> Iter<'_, K, V, MaybeTombstone, C>
  where
    C: Comparator<K>,
  {
    Iter::with_tombstone(version, self)
  }

  /// Returns an iterator over a subset of entries in the map.
  ///
  /// This iterator returns [`Entry`]s which
  /// can be used to access keys and their associated values.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::flatten::SkipMap;
  ///
  /// let numbers = SkipMap::new();
  /// numbers.insert(1, 6, "six");
  /// numbers.insert(1, 7, "seven");
  /// numbers.insert(1, 12, "twelve");
  ///
  /// // Print all numbers in the map between 5 and 8.
  /// for entry in numbers.range(1, 5..=8) {
  ///   let number = entry.key();
  ///   let number_str = entry.value();
  ///   println!("{} is {}", number, number_str);
  /// }
  /// ```
  pub fn range<Q, R>(&self, version: u64, range: R) -> Range<'_, K, V, Active, Q, R, C>
  where
    R: RangeBounds<Q>,
    C: QueryComparator<K, Q>,
    Q: ?Sized,
  {
    Range::new(version, self, range)
  }

  /// Returns an iterator over a subset of entries (with all versions) in the map.
  pub fn range_all<Q, R>(&self, version: u64, range: R) -> Range<'_, K, V, MaybeTombstone, Q, R, C>
  where
    R: RangeBounds<Q>,
    C: QueryComparator<K, Q>,
    Q: ?Sized,
  {
    Range::with_tombstone(version, self, range)
  }
}

impl<K, V, C> SkipMap<K, V, C>
where
  K: Send + 'static,
  V: Send + 'static,
  C: Comparator<K> + Send + 'static,
{
  common!("flatten");

  fn insert_in(&self, version: u64, key: K, value: V) -> Entry<'_, K, V, Active, C> {
    let ent = self.inner.insert(Key::new(key, version), Some(value));
    self.update_versions(version);
    Entry::new(ent.into(), version)
  }

  fn compare_insert_in(
    &self,
    version: u64,
    key: K,
    value: V,
    compare_fn: impl Fn(Option<&V>) -> bool,
  ) -> Entry<'_, K, V, Active, C> {
    let ent = self
      .inner
      .compare_insert(Key::new(key, version), Some(value), |old_value| {
        compare_fn(old_value.as_ref())
      });
    self.update_versions(version);
    Entry::new(ent.into(), version)
  }

  #[inline]
  fn remove_in(&self, version: u64, key: K) -> Option<Entry<'_, K, V, Active, C>> {
    let ent = self.inner.insert(Key::new(key, version), None);
    self.update_versions(version);
    let next = ent.next()?;

    if self
      .inner
      .comparator()
      .0
      .equivalent(&next.key().key, &ent.key().key)
      && next.value().is_some()
    {
      return Some(Entry::new(next.into(), version));
    }

    None
  }

  /// Removes entries with versions less than or equal to `version`.
  ///
  /// Returns the current version that `SkipMap` is compacting to.
  ///
  /// **Note**: If there is another thread is compacting, this function will just return the version that the other thread is compacting to.
  /// So the return value may not be the version that you passed in.
  pub fn compact(&self, version: u64) -> u64
  where
    V: Sync,
  {
    match self
      .last_discard_version
      .fetch_update(Ordering::SeqCst, Ordering::Acquire, |val| {
        if val >= version {
          None
        } else {
          Some(version)
        }
      }) {
      Ok(_) => {}
      // if we fail to insert the new discard version,
      // which means there is another thread that is compacting.
      // To avoid run multiple compacting at the same time, we just return.
      Err(version) => return version,
    }

    let min_version = self.min_version.load(Ordering::Acquire);
    for ent in self.inner.iter() {
      if ent.key().version <= version {
        ent.remove();
      }
    }

    let _ =
      self
        .min_version
        .compare_exchange(min_version, version, Ordering::AcqRel, Ordering::Relaxed);
    version
  }
}
