use core::{
  fmt::Debug,
  ops::{Bound, RangeBounds},
  sync::atomic::{AtomicU64, Ordering},
};

use crossbeam_skiplist::{map::Entry as CEntry, Comparable, SkipMap as CSkipMap};

mod iter;
pub use iter::*;

use crate::error::Error;

#[cfg(test)]
mod tests;

/// A reference-counted entry in a map.
pub struct Entry<'a, K, V> {
  ent: CEntry<'a, K, Values<V>>,
  value: CEntry<'a, u64, Option<V>>,
  query_version: u64,
}

impl<K, V> Clone for Entry<'_, K, V> {
  fn clone(&self) -> Self {
    Self {
      ent: self.ent.clone(),
      value: self.value.clone(),
      query_version: self.query_version,
    }
  }
}

impl<K: Debug, V: Debug> Debug for Entry<'_, K, V> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("Entry")
      .field("version", &self.version())
      .field("key", self.key())
      .field("value", self.value())
      .finish()
  }
}

impl<'a, K, V> Entry<'a, K, V> {
  /// Returns the version of the entry.
  #[inline]
  pub fn version(&self) -> u64 {
    *self.value.key()
  }

  /// Returns a reference to the key.
  #[inline]
  pub fn key(&self) -> &'a K {
    self.ent.key()
  }

  /// Returns a reference to the value.
  #[inline]
  pub fn value(&self) -> &'a V {
    self
      .value
      .value()
      .as_ref()
      .expect("value is null, please report bug to https://github.com/al8n/crossbeam-skiplist-mvcc")
  }

  #[inline]
  fn new(
    ent: CEntry<'a, K, Values<V>>,
    value: CEntry<'a, u64, Option<V>>,
    query_version: u64,
  ) -> Self {
    Self {
      ent,
      value,
      query_version,
    }
  }
}

impl<'a, K, V> Entry<'a, K, V>
where
  K: Ord,
{
  /// Returns the next entry in the map.
  pub fn next(&self) -> Option<Entry<'a, K, V>> {
    let mut ent = self.ent.next();
    loop {
      match ent {
        Some(entry) => {
          let value = entry
            .value()
            .upper_bound(Bound::Included(&self.query_version));
          match value {
            Some(value) if value.value().is_some() => {
              return Some(Entry::new(entry, value, self.query_version))
            }
            _ => ent = entry.next(),
          }
        }
        None => return None,
      }
    }
  }

  /// Returns the previous entry in the map.
  pub fn prev(&self) -> Option<Entry<'a, K, V>> {
    let mut ent = self.ent.prev();
    loop {
      match ent {
        Some(entry) => {
          let value = entry
            .value()
            .upper_bound(Bound::Included(&self.query_version));
          match value {
            Some(value) if value.value().is_some() => {
              return Some(Entry::new(entry, value, self.query_version))
            }
            _ => ent = entry.prev(),
          }
        }
        None => return None,
      }
    }
  }
}

/// A reference-counted entry which may return optional value in a map.
pub struct VersionedEntry<'a, K, V> {
  ent: CEntry<'a, K, Values<V>>,
  value: CEntry<'a, u64, Option<V>>,
  query_version: u64,
}

impl<K, V> Clone for VersionedEntry<'_, K, V> {
  fn clone(&self) -> Self {
    Self {
      ent: self.ent.clone(),
      value: self.value.clone(),
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
    *self.value.key()
  }

  /// Returns a reference to the key.
  #[inline]
  pub fn key(&self) -> &'a K {
    self.ent.key()
  }

  /// Returns a reference to the value.
  #[inline]
  pub fn value(&self) -> Option<&'a V> {
    self.value.value().as_ref()
  }

  #[inline]
  const fn new(
    ent: CEntry<'a, K, Values<V>>,
    value: CEntry<'a, u64, Option<V>>,
    query_version: u64,
  ) -> Self {
    Self {
      ent,
      value,
      query_version,
    }
  }
}

impl<'a, K, V> VersionedEntry<'a, K, V>
where
  K: Ord,
{
  /// Returns the next entry in the map.
  pub fn next(&self) -> Option<VersionedEntry<'a, K, V>> {
    let mut curr = self.ent.clone();
    let mut next_value = self.value.prev();
    loop {
      match next_value {
        Some(value) => {
          return Some(VersionedEntry::new(curr, value, self.query_version));
        }
        None => {
          curr = curr.next()?;
          next_value = curr
            .value()
            .upper_bound(Bound::Included(&self.query_version));
        }
      }
    }
  }

  /// Returns the previous entry in the map.
  pub fn prev(&self) -> Option<VersionedEntry<'a, K, V>> {
    let mut curr = self.ent.clone();
    let mut next_value = self.value.next();
    loop {
      match next_value {
        Some(value) => {
          return Some(VersionedEntry::new(curr, value, self.query_version));
        }
        None => {
          curr = curr.prev()?;
          next_value = curr.value().range(..=self.query_version).next();
        }
      }
    }
  }
}

type Values<V> = CSkipMap<u64, Option<V>>;

/// A multiple version ordered map based on a lock-free skip list.
///
/// For the difference between `nested::SkipMap` and `flatten::SkipMap`, see the [crate-level documentation](crate).
pub struct SkipMap<K, V> {
  inner: CSkipMap<K, Values<V>>,
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
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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

    match self.inner.get(key) {
      Some(ent) => {
        matches!(ent.value().upper_bound(Bound::Included(&version)), Some(ent) if ent.value().is_some())
      }
      None => false,
    }
  }

  /// Returns `true` if the map contains a value for the specified key even though this entry already been marked as removed.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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

    match self.inner.get(key) {
      Some(ent) => ent.value().upper_bound(Bound::Included(&version)).is_some(),
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
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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

    match self.inner.get(key) {
      Some(ent) => {
        let value = ent.value().upper_bound(Bound::Included(&version));
        match value {
          Some(value) if value.value().is_some() => Some(Entry::new(ent, value, version)),
          _ => None,
        }
      }
      _ => None,
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
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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

    match self.inner.get(key) {
      Some(ent) => {
        let value = ent.value().upper_bound(Bound::Included(&version));
        value.map(|value| VersionedEntry::new(ent, value, version))
      }
      _ => None,
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
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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

    let mut ent = self.inner.lower_bound(bound);

    loop {
      match ent {
        Some(entry) => {
          let value = entry.value().upper_bound(Bound::Included(&version));
          match value {
            Some(value) if value.value().is_some() => {
              return Some(Entry::new(entry, value, version))
            }
            _ => ent = entry.next(),
          }
        }
        None => return None,
      }
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
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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

    let mut ent = self.inner.lower_bound(bound);

    loop {
      match ent {
        Some(entry) => {
          let value = entry.value().upper_bound(Bound::Included(&version));
          match value {
            Some(value) => return Some(VersionedEntry::new(entry, value, version)),
            _ => ent = entry.next(),
          }
        }
        None => return None,
      }
    }
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
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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

    let mut ent = self.inner.upper_bound(bound);

    loop {
      match ent {
        Some(entry) => {
          let value = entry.value().upper_bound(Bound::Included(&version));
          match value {
            Some(value) if value.value().is_some() => {
              return Some(Entry::new(entry, value, version))
            }
            _ => ent = entry.prev(),
          }
        }
        None => return None,
      }
    }
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
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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

    let mut ent = self.inner.upper_bound(bound);

    loop {
      match ent {
        Some(entry) => {
          let value = entry.value().upper_bound(Bound::Included(&version));
          match value {
            Some(value) => return Some(VersionedEntry::new(entry, value, version)),
            _ => ent = entry.prev(),
          }
        }
        None => return None,
      }
    }
  }

  /// Returns the entry with the smallest key.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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

    let mut curr = self.inner.front();

    loop {
      match curr {
        Some(ent) => {
          let value = ent.value().upper_bound(Bound::Included(&version));
          match value {
            Some(value) if value.value().is_some() => return Some(Entry::new(ent, value, version)),
            _ => curr = ent.next(),
          }
        }
        None => return None,
      }
    }
  }

  /// Returns the entry with the smallest key.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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

    let mut curr = self.inner.front();

    loop {
      match curr {
        Some(ent) => {
          let value = ent.value().upper_bound(Bound::Included(&version));
          match value {
            Some(value) => return Some(VersionedEntry::new(ent, value, version)),
            _ => curr = ent.next(),
          }
        }
        None => return None,
      }
    }
  }

  /// Returns the entry with the largest key.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
  ///
  /// let numbers = SkipMap::new();
  /// numbers.insert(1, 5, "five");
  /// assert_eq!(*numbers.back(1).unwrap().value(), "five");
  /// numbers.insert(1, 6, "six");
  /// assert_eq!(*numbers.back(1).unwrap().value(), "six");
  /// ```
  pub fn back(&self, version: u64) -> Option<Entry<'_, K, V>> {
    if !self.may_contain_version(version) {
      println!("min_version {}", self.min_version.load(Ordering::Acquire));
      return None;
    }

    let mut curr = self.inner.back();

    loop {
      match curr {
        Some(ent) => {
          let value = ent.value().upper_bound(Bound::Included(&version));
          match value {
            Some(value) if value.value().is_some() => return Some(Entry::new(ent, value, version)),
            _ => curr = ent.prev(),
          }
        }
        None => return None,
      }
    }
  }

  /// Returns the entry with the largest key.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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

    let mut curr = self.inner.back();

    loop {
      match curr {
        Some(ent) => {
          let value = ent.value().range(..=version).next();
          match value {
            Some(value) => return Some(VersionedEntry::new(ent, value, version)),
            _ => curr = ent.prev(),
          }
        }
        None => return None,
      }
    }
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
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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
    Iter::new(self.inner.iter(), version)
  }

  /// Returns an iterator over all entries (all versions) in the map.
  pub fn iter_all_versions(&self, version: u64) -> IterAll<'_, K, V> {
    IterAll::new(self.inner.iter(), version)
  }

  /// Returns an iterator over a subset of entries in the map.
  ///
  /// This iterator returns [`Entry`]s which
  /// can be used to access keys and their associated values.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use crossbeam_skiplist_mvcc::nested::SkipMap;
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
    Range::new(self.inner.range(range), version)
  }

  /// Returns an iterator over a subset of entries (with all versions) in the map.
  pub fn range_all_versions<Q, R>(&self, version: u64, range: R) -> RangeAll<'_, Q, R, K, V>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K>,
  {
    RangeAll::new(self.inner.range(range), version)
  }
}

impl<K, V> SkipMap<K, V>
where
  K: Ord + Send + 'static,
  V: Send + 'static,
{
  common!("nested");

  fn insert_in(&self, version: u64, key: K, value: V) -> Entry<'_, K, V> {
    let mut exist = true;
    let ent = self.inner.get_or_insert_with(key, || {
      exist = false;
      Values::new()
    });
    let value = ent.value().insert(version, Some(value));
    self.update_versions(version);
    Entry::new(ent, value, version)
  }

  fn compare_insert_in<F>(&self, version: u64, key: K, value: V, compare_fn: F) -> Entry<'_, K, V>
  where
    F: Fn(Option<&V>) -> bool,
  {
    let mut exist = true;
    let ent = self.inner.get_or_insert_with(key, || {
      exist = false;
      Values::new()
    });

    let value = ent
      .value()
      .compare_insert(version, Some(value), |val| compare_fn(val.as_ref()));
    self.update_versions(version);
    Entry::new(ent, value, version)
  }

  #[inline]
  fn remove_in(&self, version: u64, key: K) -> Option<Entry<'_, K, V>> {
    let mut exist = true;
    let ent = self.inner.get_or_insert_with(key, || {
      exist = false;
      Values::new()
    });
    let values = ent.value();
    let old = if values.is_empty() {
      None
    } else {
      values
        .upper_bound(Bound::Included(&version))
        .and_then(|value| {
          value
            .value()
            .is_some()
            .then(|| Entry::new(ent, value, version))
        })
    };

    values.insert(version, None);
    self.update_versions(version);
    old
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
      let values = ent.value();
      let len = values.len();
      for (idx, ent) in values.iter().enumerate() {
        // we reach the end of the list
        if idx == len - 1 {
          if ent.value().is_none() {
            ent.remove();
          }
          break;
        }

        let ent_version = *ent.key();
        if ent_version > version {
          break;
        }

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
