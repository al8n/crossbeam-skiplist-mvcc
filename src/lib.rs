#![doc = include_str!("../README.md")]
#![forbid(unsafe_code)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]

macro_rules! common {
  ($mod_name: literal) => {
    /// Inserts a `key`-`value` pair into the map and returns the new entry.
    ///
    /// If there is an existing entry with this key, it will be removed before inserting the new
    /// one.
    ///
    /// This function returns an [`Ok(Entry)`](Entry) which
    /// can be used to access the inserted key's associated value.
    ///
    /// This function returns an [`Err(Error)`](Error) if the given version has already been discarded by [`compact`](SkipMap::compact).
    ///
    /// See also [`insert_unchecked`](SkipMap::insert_unchecked).
    ///
    /// ## Example
    ///
    /// ```rust
    #[doc = concat!("use crossbeam_skiplist_mvcc::", $mod_name, "::SkipMap;")]
    ///
    /// let map = SkipMap::new();
    /// map.insert(1, "key", "value").unwrap();
    ///
    /// assert_eq!(*map.get(1, "key").unwrap().value(), "value");
    /// ```
    pub fn insert(&self, version: u64, key: K, value: V) -> Result<Entry<'_, K, V>, Error> {
      self
        .check_discard(version)
        .map(|_| self.insert_in(version, key, value))
    }

    /// Inserts a `key`-`value` pair into the map and returns the new entry.
    ///
    /// If there is an existing entry with this key, it will be removed before inserting the new
    /// one.
    ///
    /// This function returns an [`Entry`] which
    /// can be used to access the inserted key's associated value.
    ///
    /// See also [`insert`](SkipMap::insert).
    ///
    /// ## Panics
    /// - If the given `version` has already been discarded by [`compact`](SkipMap::compact).
    ///
    /// ## Example
    ///
    /// ```rust
    #[doc = concat!("use crossbeam_skiplist_mvcc::", $mod_name, "::SkipMap;")]
    ///
    /// let map = SkipMap::new();
    /// map.insert_unchecked(1, "key", "value");
    ///
    /// assert_eq!(*map.get(1, "key").unwrap().value(), "value");
    /// ```
    pub fn insert_unchecked(&self, version: u64, key: K, value: V) -> Entry<'_, K, V> {
      self
        .check_discard(version)
        .expect("version has already been discarded");
      self.insert_in(version, key, value)
    }

    /// Inserts a `key`-`value` pair into the skip list and returns the new entry.
    ///
    /// If there is an existing entry with this key and compare(entry.value) returns true,
    /// it will be removed before inserting the new one.
    /// The closure will not be called if the key is not present.
    ///
    /// This function returns an [`Ok(Entry)`](`Entry`) which
    /// can be used to access the inserted key's associated value.
    ///
    /// This function returns an [`Err(Error)`](`Error`) if the given version has already been discarded by [`compact`](SkipMap::compact).
    ///
    /// See also [`compare_insert_unchecked`](SkipMap::compare_insert_unchecked).
    ///
    /// ## Example
    ///
    /// ```rust
    #[doc = concat!("use crossbeam_skiplist_mvcc::", $mod_name, "::SkipMap;")]
    ///
    /// let map = SkipMap::new();
    /// map.insert(1, "key", 1);
    /// map.compare_insert(1, "key", 0, |x| x.unwrap() < &0).unwrap();
    /// assert_eq!(*map.get(1, "key").unwrap().value(), 1);
    /// map.compare_insert(1, "key", 2, |x| x.unwrap() < &2).unwrap();
    /// assert_eq!(*map.get(1, "key").unwrap().value(), 2);
    /// map.compare_insert(1, "absent_key", 0, |_| false).unwrap();
    /// assert_eq!(*map.get(1, "absent_key").unwrap().value(), 0);
    /// ```
    pub fn compare_insert<F>(
      &self,
      version: u64,
      key: K,
      value: V,
      compare_fn: F,
    ) -> Result<Entry<'_, K, V>, Error>
    where
      F: Fn(Option<&V>) -> bool,
    {
      self
        .check_discard(version)
        .map(|_| self.compare_insert_in(version, key, value, compare_fn))
    }

    /// Inserts a `key`-`value` pair into the skip list and returns the new entry.
    ///
    /// If there is an existing entry with this key and compare(entry.value) returns true,
    /// it will be removed before inserting the new one.
    /// The closure will not be called if the key is not present.
    ///
    /// This function returns an [`Entry`] which
    /// can be used to access the inserted key's associated value.
    ///
    /// ## Example
    ///
    /// ```rust
    #[doc = concat!("use crossbeam_skiplist_mvcc::", $mod_name, "::SkipMap;")]
    ///
    /// let map = SkipMap::new();
    /// map.insert(1, "key", 1);
    /// map.compare_insert_unchecked(1, "key", 0, |x| x.unwrap() < &0);
    /// assert_eq!(*map.get(1, "key").unwrap().value(), 1);
    /// map.compare_insert_unchecked(1, "key", 2, |x| x.unwrap() < &2);
    /// assert_eq!(*map.get(1, "key").unwrap().value(), 2);
    /// map.compare_insert_unchecked(1, "absent_key", 0, |_| false);
    /// assert_eq!(*map.get(1, "absent_key").unwrap().value(), 0);
    /// ```
    pub fn compare_insert_unchecked<F>(
      &self,
      version: u64,
      key: K,
      value: V,
      compare_fn: F,
    ) -> Entry<'_, K, V>
    where
      F: Fn(Option<&V>) -> bool,
    {
      self
        .check_discard(version)
        .expect("version has already been discarded");
      self.compare_insert_in(version, key, value, compare_fn)
    }

    /// Insert a tombstone entry for the specified `key` from the map and returns it.
    ///
    /// Note that this will not actually remove the entry from the map,
    /// but only insert a new entry and mark it as removed.
    /// To actually remove entries with old versions, use [`compact`](SkipMap::compact).
    ///
    /// This function returns an [`Entry`] which
    /// can be used to access the removed key's associated value.
    ///
    /// This function returns an [`Err(Error)`](`Error`) if the given version has already been discarded by [`compact`](SkipMap::compact).
    ///
    /// See also [`remove_unchecked`](SkipMap::remove_unchecked).
    ///
    /// ## Example
    ///
    /// ```rust
    #[doc = concat!("use crossbeam_skiplist_mvcc::", $mod_name, "::SkipMap;")]
    ///
    /// let map: SkipMap<&str, &str> = SkipMap::new();
    /// assert!(map.remove(1, "invalid key").unwrap().is_none());
    ///
    /// map.insert(0, "key", "value");
    /// assert_eq!(*map.remove(1, "key").unwrap().unwrap().value(), "value");
    /// ```
    pub fn remove(&self, version: u64, key: K) -> Result<Option<Entry<'_, K, V>>, Error> {
      self
        .check_discard(version)
        .map(|_| self.remove_in(version, key))
    }

    /// Insert a tombstone entry for the specified `key` from the map and returns it.
    ///
    /// Note that this will not actually remove the entry from the map,
    /// but only insert a new entry and mark it as removed.
    /// To actually remove entries with old versions, use [`compact`](SkipMap::compact).
    ///
    /// This function returns an [`Entry`] which
    /// can be used to access the removed key's associated value.
    ///
    /// ## Panics
    /// - If the given `version` has already been discarded by [`compact`](SkipMap::compact).
    ///
    /// ## Example
    ///
    /// ```rust
    #[doc = concat!("use crossbeam_skiplist_mvcc::", $mod_name, "::SkipMap;")]
    ///
    /// let map: SkipMap<&str, &str> = SkipMap::new();
    /// assert!(map.remove_unchecked(1, "invalid key").is_none());
    ///
    /// map.insert(0, "key", "value");
    /// assert_eq!(*map.remove_unchecked(1, "key").unwrap().value(), "value");
    /// ```
    pub fn remove_unchecked(&self, version: u64, key: K) -> Option<Entry<'_, K, V>> {
      self
        .check_discard(version)
        .expect("version has already been discarded");
      self.remove_in(version, key)
    }

    #[inline]
    fn check_discard(&self, version: u64) -> Result<(), Error> {
      let last = self.last_discard_version.load(Ordering::Acquire);
      if last != 0 && last >= version {
        return Err(Error::AlreadyDiscarded(version));
      }
      Ok(())
    }
  };
}

/// A multiple version ordered map based on a lock-free skip list. See [`SkipMap`](crate::nested::SkipMap).
pub mod nested;

/// A multiple version ordered map based on a lock-free skip list. See [`SkipMap`](crate::flatten::SkipMap).
pub mod flatten;

/// Error types for this crate.
pub mod error;
