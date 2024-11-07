use core::{
  cmp,
  fmt::Debug,
  marker::PhantomData,
  ops::{Bound, RangeBounds},
  sync::atomic::{AtomicU64, Ordering},
};

use crossbeam_skiplist::{map::Entry as CEntry, Comparable, Equivalent, SkipMap as CSkipMap};

mod iter;
pub use iter::*;

use crate::error::Error;

#[cfg(test)]
mod tests;

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

impl<K> PartialEq for Key<K>
where
  K: PartialEq,
{
  #[inline]
  fn eq(&self, other: &Self) -> bool {
    self.key == other.key && self.version == other.version
  }
}

impl<K> Eq for Key<K> where K: Eq {}

impl<K> PartialOrd for Key<K>
where
  K: PartialOrd,
{
  #[inline]
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
    self
      .key
      .partial_cmp(&other.key)
      .map(|o| o.then_with(|| other.version.cmp(&self.version)))
  }
}

impl<K> Ord for Key<K>
where
  K: Ord,
{
  #[inline]
  fn cmp(&self, other: &Self) -> cmp::Ordering {
    self
      .key
      .cmp(&other.key)
      .then_with(|| other.version.cmp(&self.version))
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

impl<Q, K> Equivalent<Key<K>> for Query<'_, Q, K>
where
  Q: ?Sized + Equivalent<K>,
{
  #[inline]
  fn equivalent(&self, key: &Key<K>) -> bool {
    Equivalent::equivalent(self.query, &key.key) && key.version == self.version
  }
}

impl<Q, K> Comparable<Key<K>> for Query<'_, Q, K>
where
  Q: ?Sized + Comparable<K>,
{
  #[inline]
  fn compare(&self, key: &Key<K>) -> cmp::Ordering {
    Comparable::compare(self.query, &key.key).then_with(|| key.version.cmp(&self.version))
  }
}

/// A reference-counted entry in a map.
pub struct Entry<'a, K, V>(VersionedEntry<'a, K, V>);

impl<K: Debug, V: Debug> Debug for Entry<'_, K, V> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("Entry")
      .field("version", &self.version())
      .field("key", self.key())
      .field("value", &self.value())
      .finish()
  }
}

impl<K, V> Clone for Entry<'_, K, V> {
  #[inline]
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, K, V> Entry<'a, K, V> {
  /// Returns the version of the entry.
  #[inline]
  pub fn version(&self) -> u64 {
    self.0.version()
  }

  /// Returns a reference to the key.
  #[inline]
  pub fn key(&self) -> &'a K {
    self.0.key()
  }

  /// Returns a reference to the value.
  #[inline]
  pub fn value(&self) -> &'a V {
    self
      .0
      .value()
      .expect("value is null, please report bug to https://github.com/al8n/crossbeam-skiplist-mvcc")
  }

  #[inline]
  fn new(entry: CEntry<'a, Key<K>, Option<V>>, query_version: u64) -> Self {
    Self(VersionedEntry::new(entry, query_version))
  }
}

impl<K, V> Entry<'_, K, V>
where
  K: Ord,
{
  /// Returns the next entry in the map.
  pub fn next(&self) -> Option<Self> {
    self.0.next_in(false).map(Entry)
  }

  /// Returns the previous entry in the map.
  pub fn prev(&self) -> Option<Self> {
    self.0.prev_in(false).map(Entry)
  }
}

/// A reference-counted entry which may return optional value in a map.
pub struct VersionedEntry<'a, K, V> {
  ent: CEntry<'a, Key<K>, Option<V>>,
  query_version: u64,
}

impl<K, V> Clone for VersionedEntry<'_, K, V> {
  #[inline]
  fn clone(&self) -> Self {
    Self {
      ent: self.ent.clone(),
      query_version: self.query_version,
    }
  }
}

impl<K: Debug, V: Debug> Debug for VersionedEntry<'_, K, V> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("VersionedEntry")
      .field("version", &self.version())
      .field("key", self.key())
      .field("value", &self.value())
      .finish()
  }
}

impl<'a, K, V> VersionedEntry<'a, K, V> {
  /// Returns the version of the entry.
  #[inline]
  pub fn version(&self) -> u64 {
    self.ent.key().version
  }

  /// Returns a reference to the key.
  #[inline]
  pub fn key(&self) -> &'a K {
    &self.ent.key().key
  }

  /// Returns a reference to the value.
  #[inline]
  pub fn value(&self) -> Option<&'a V> {
    self.ent.value().as_ref()
  }

  #[inline]
  const fn new(ent: CEntry<'a, Key<K>, Option<V>>, query_version: u64) -> Self {
    Self { ent, query_version }
  }
}

impl<K, V> VersionedEntry<'_, K, V>
where
  K: Ord,
{
  /// Returns the next entry in the map.
  pub fn next(&self) -> Option<Self> {
    self.next_in(true)
  }

  /// Returns the previous entry in the map.
  pub fn prev(&self) -> Option<Self> {
    self.prev_in(true)
  }

  fn next_in(&self, all_versions: bool) -> Option<Self> {
    if all_versions {
      let nd = self.ent.next();
      SkipMap::find_next(nd, self.query_version, |_| true)
    } else {
      let nd = self.ent.next();
      SkipMap::find_next_max_version(nd, self.query_version, |_| true)
    }
    .map(|ent| VersionedEntry::new(ent, self.query_version))
  }

  fn prev_in(&self, all_versions: bool) -> Option<Self> {
    if all_versions {
      let nd = self.ent.prev();
      SkipMap::find_prev(nd, self.query_version, |_| true)
    } else {
      let nd = self.ent.prev();
      SkipMap::find_prev_max_version(nd, self.query_version, |_| true)
    }
    .map(|ent| VersionedEntry::new(ent, self.query_version))
  }
}

/// A multiple version ordered map based on a lock-free skip list.
///
/// For the difference between `nested::SkipMap` and `flatten::SkipMap`, see the [crate-level documentation](crate).
pub struct SkipMap<K, V> {
  inner: CSkipMap<Key<K>, Option<V>>,
  min_version: AtomicU64,
  max_version: AtomicU64,
  last_discard_version: AtomicU64,
}

impl<K, V> Default for SkipMap<K, V> {
  #[inline]
  fn default() -> Self {
    Self::new()
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
      inner: CSkipMap::new(),
      min_version: AtomicU64::new(u64::MAX),
      max_version: AtomicU64::new(0),
      last_discard_version: AtomicU64::new(0),
    }
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

impl<K, V> SkipMap<K, V>
where
  K: Ord,
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
    Q: ?Sized + Comparable<K>,
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
        if !key.equivalent(&k.key) {
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
  /// assert!(ages.contains_key_versioned(0, &"Bill Gates"));
  /// assert!(ages.contains_key_versioned(1, &"Bill Gates"));
  /// assert!(!ages.contains_key_versioned(1, &"Steve Jobs"));
  /// ```
  #[inline]
  pub fn contains_key_versioned<Q>(&self, version: u64, key: &Q) -> bool
  where
    Q: ?Sized + Comparable<K>,
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
        if !key.equivalent(&k.key) {
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
  pub fn get<Q>(&self, version: u64, key: &Q) -> Option<Entry<'_, K, V>>
  where
    Q: ?Sized + Comparable<K>,
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
        if !key.equivalent(&k.key) {
          return None;
        }

        if entry.value().is_none() {
          return None;
        }

        Some(Entry::new(entry, version))
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
  /// assert!(numbers.get_versioned(0, "six").is_none());
  ///
  /// numbers.insert(0, "six", 6);
  /// numbers.remove(1, "six");
  ///
  /// assert!(numbers.get(1, "six").is_none());
  /// assert!(numbers.get_versioned(1, "six").unwrap().value().is_none());
  /// ```
  pub fn get_versioned<Q>(&self, version: u64, key: &Q) -> Option<VersionedEntry<'_, K, V>>
  where
    Q: ?Sized + Comparable<K>,
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
        if !key.equivalent(&k.key) {
          return None;
        }

        Some(VersionedEntry::new(entry, version))
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
  pub fn lower_bound<'a, Q>(&'a self, version: u64, bound: Bound<&Q>) -> Option<Entry<'a, K, V>>
  where
    Q: ?Sized + Comparable<K>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.iter(version).0.seek_lower_bound(bound).map(Entry)
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
  /// let greater_than_five = numbers.lower_bound_versioned(0, Excluded(&5)).unwrap();
  /// assert_eq!(*greater_than_five.value().unwrap(), "six");
  ///
  /// let greater_than_six = numbers.lower_bound_versioned(0, Excluded(&6)).unwrap();
  /// assert_eq!(*greater_than_six.value().unwrap(), "seven");
  ///
  /// let greater_than_thirteen = numbers.lower_bound_versioned(0, Excluded(&13));
  /// assert!(greater_than_thirteen.is_none());
  /// ```
  pub fn lower_bound_versioned<'a, Q>(
    &'a self,
    version: u64,
    bound: Bound<&Q>,
  ) -> Option<VersionedEntry<'a, K, V>>
  where
    Q: ?Sized + Comparable<K>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.iter_all_versions(version).0.seek_lower_bound(bound)
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
  pub fn upper_bound<'a, Q>(&'a self, version: u64, bound: Bound<&Q>) -> Option<Entry<'a, K, V>>
  where
    Q: ?Sized + Comparable<K>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.iter(version).0.seek_upper_bound(bound).map(Entry)
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
  /// let less_than_eight = numbers.upper_bound_versioned(0, Excluded(&8)).unwrap();
  /// assert_eq!(*less_than_eight.value().unwrap(), "seven");
  ///
  /// let less_than_six = numbers.upper_bound_versioned(0, Excluded(&6));
  /// assert!(less_than_six.is_none());
  /// ```
  pub fn upper_bound_versioned<'a, Q>(
    &'a self,
    version: u64,
    bound: Bound<&Q>,
  ) -> Option<VersionedEntry<'a, K, V>>
  where
    Q: ?Sized + Comparable<K>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.iter_all_versions(version).0.seek_upper_bound(bound)
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
  pub fn front(&self, version: u64) -> Option<Entry<'_, K, V>> {
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
  /// assert_eq!(*numbers.front_versioned(1).unwrap().value().unwrap(), "five");
  /// numbers.insert(1, 6, "six");
  /// assert_eq!(*numbers.front_versioned(1).unwrap().value().unwrap(), "five");
  /// ```
  pub fn front_versioned(&self, version: u64) -> Option<VersionedEntry<'_, K, V>> {
    if !self.may_contain_version(version) {
      return None;
    }

    self.iter_all_versions(version).next()
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
  pub fn back(&self, version: u64) -> Option<Entry<'_, K, V>> {
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
  /// assert_eq!(*numbers.back_versioned(1).unwrap().value().unwrap(), "five");
  /// numbers.insert(1, 6, "six");
  /// assert_eq!(*numbers.back_versioned(1).unwrap().value().unwrap(), "six");
  /// ```
  pub fn back_versioned(&self, version: u64) -> Option<VersionedEntry<'_, K, V>> {
    if !self.may_contain_version(version) {
      return None;
    }

    self.iter_all_versions(version).next_back()
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
  pub fn iter(&self, version: u64) -> Iter<'_, K, V> {
    Iter::new(self, version)
  }

  /// Returns an iterator over all entries (all versions) in the map.
  pub fn iter_all_versions(&self, version: u64) -> IterAll<'_, K, V> {
    IterAll::new(self, version)
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
  pub fn range<Q, R>(&self, version: u64, range: R) -> Range<'_, Q, R, K, V>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K>,
  {
    Range::new(range, self, version)
  }

  /// Returns an iterator over a subset of entries (with all versions) in the map.
  pub fn range_all_versions<Q, R>(&self, version: u64, range: R) -> RangeAll<'_, Q, R, K, V>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K>,
  {
    RangeAll::new(range, self, version)
  }

  fn find_next_max_version(
    mut curr: Option<CEntry<'_, Key<K>, Option<V>>>,
    version: u64,
    contains_key: impl Fn(&K) -> bool,
  ) -> Option<CEntry<'_, Key<K>, Option<V>>> {
    while let Some(ent) = curr {
      let curr_key = ent.key();
      // if the current version is larger than the query version, we should move next to find a smaller version.
      if curr_key.version > version {
        curr = ent.next();
        continue;
      }

      // if the entry with largest version is removed or the trailer is invalid, we should skip this key.
      if ent.value().is_none() {
        let mut next = ent.next();
        loop {
          match next {
            None => return None,
            Some(next_ent) => {
              // if next's key is different from the current key, we should break the loop
              if next_ent.key().key != curr_key.key {
                curr = Some(next_ent);
                break;
              }

              next = next_ent.next();
            }
          }
        }

        continue;
      }

      if contains_key(&curr_key.key) {
        return Some(ent);
      }

      curr = ent.next();
    }

    None
  }

  fn find_next(
    mut curr: Option<CEntry<'_, Key<K>, Option<V>>>,
    version: u64,
    contains_key: impl Fn(&K) -> bool,
  ) -> Option<CEntry<'_, Key<K>, Option<V>>> {
    while let Some(ent) = curr {
      let curr_key = ent.key();
      if curr_key.version > version {
        curr = ent.next();
        continue;
      }

      if contains_key(&curr_key.key) {
        return Some(ent);
      }

      curr = ent.next();
    }

    None
  }

  fn find_prev_max_version(
    mut curr: Option<CEntry<'_, Key<K>, Option<V>>>,
    version: u64,
    contains_key: impl Fn(&K) -> bool,
  ) -> Option<CEntry<'_, Key<K>, Option<V>>> {
    while let Some(ent) = curr {
      let curr_key = ent.key();
      if curr_key.version > version {
        curr = ent.prev();
        continue;
      }

      let prev = ent.prev();

      match prev {
        None => {
          // prev is null or the head, we should try to see if we can return the current node.
          if ent.value().is_some() {
            // the current node is valid, we should return it.
            if contains_key(&curr_key.key) {
              return Some(ent);
            }
          }

          return None;
        }
        Some(prev) => {
          // At this point, prev is not null and not the head.
          // if the prev's version is greater than the query version or the prev's key is different from the current key,
          // we should try to return the current node.
          let prev_key = prev.key();
          if (prev_key.version > version || curr_key.key.ne(&prev_key.key))
            && ent.value().is_some()
            && contains_key(&curr_key.key)
          {
            return Some(ent);
          }

          curr = Some(prev);
        }
      }
    }

    None
  }

  fn find_prev(
    mut curr: Option<CEntry<'_, Key<K>, Option<V>>>,
    version: u64,
    contains_key: impl Fn(&K) -> bool,
  ) -> Option<CEntry<'_, Key<K>, Option<V>>> {
    while let Some(ent) = curr {
      let curr_key = ent.key();
      if curr_key.version > version {
        curr = ent.prev();
        continue;
      }

      if contains_key(&curr_key.key) {
        return Some(ent);
      }

      curr = ent.prev();
    }

    None
  }
}

impl<K, V> SkipMap<K, V>
where
  K: Ord + Send + 'static,
  V: Send + 'static,
{
  common!("flatten");

  fn insert_in(&self, version: u64, key: K, value: V) -> Entry<'_, K, V> {
    let ent = self.inner.insert(Key::new(key, version), Some(value));
    self.update_versions(version);
    Entry::new(ent, version)
  }

  fn compare_insert_in(
    &self,
    version: u64,
    key: K,
    value: V,
    compare_fn: impl Fn(Option<&V>) -> bool,
  ) -> Entry<'_, K, V> {
    let ent = self
      .inner
      .compare_insert(Key::new(key, version), Some(value), |old_value| {
        compare_fn(old_value.as_ref())
      });
    self.update_versions(version);
    Entry::new(ent, version)
  }

  #[inline]
  fn remove_in(&self, version: u64, key: K) -> Option<Entry<'_, K, V>> {
    let ent = self.inner.insert(Key::new(key, version), None);
    self.update_versions(version);
    let next = ent.next()?;
    if next.key().key.eq(&ent.key().key) && next.value().is_some() {
      return Some(Entry::new(next, version));
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
