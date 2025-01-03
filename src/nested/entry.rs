use core::{fmt::Debug, marker::PhantomData, ops::Bound};

use crossbeam_skiplist::{equivalentor::Comparator, map::Entry as CEntry, Ascend};
use dbutils::state::State;

use crate::Transfer;

use super::Values;

/// A reference-counted entry.
pub struct Entry<'a, K, V, S, C> {
  ent: CEntry<'a, K, Values<V>, C>,
  value: CEntry<'a, u64, Option<V>, Ascend>,
  query_version: u64,
  _s: PhantomData<S>,
}

impl<K, V, S, C> Clone for Entry<'_, K, V, S, C> {
  fn clone(&self) -> Self {
    Self {
      ent: self.ent.clone(),
      value: self.value.clone(),
      query_version: self.query_version,
      _s: PhantomData,
    }
  }
}

impl<'a, K, V, S, C> Debug for Entry<'a, K, V, S, C>
where
  K: Debug,
  V: Debug,
  S: Transfer<'a, V>,
  S::To: Debug,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("Entry")
      .field("version", &self.version())
      .field("key", &self.key())
      .field("value", &self.value())
      .finish()
  }
}

impl<'a, K, V, S, C> Entry<'a, K, V, S, C> {
  /// Returns the version of the entry.
  #[inline]
  pub fn version(&self) -> u64 {
    *self.value.key()
  }

  /// Returns the key of the entry.
  #[inline]
  pub fn key(&self) -> &'a K {
    self.ent.key()
  }

  /// Returns the value of the entry.
  #[inline]
  pub fn value(&self) -> S::To
  where
    S: Transfer<'a, V>,
  {
    S::output(self.value.value().as_ref())
  }

  /// Returns a reference to the comparator.
  #[inline]
  pub fn comparator(&self) -> &'a C {
    self.ent.comparator()
  }

  #[inline]
  pub(super) const fn new(
    ent: CEntry<'a, K, Values<V>, C>,
    value: CEntry<'a, u64, Option<V>, Ascend>,
    query_version: u64,
  ) -> Self {
    Self {
      ent,
      value,
      query_version,
      _s: PhantomData,
    }
  }
}

impl<'a, K, V, S, C> Entry<'a, K, V, S, C>
where
  C: Comparator<K>,
  S: State,
{
  /// Returns the next entry in the map.
  pub fn next(&self) -> Option<Entry<'a, K, V, S, C>> {
    if S::ALWAYS_VALID {
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
    } else {
      let mut curr = self.ent.clone();
      let mut next_value = self.value.prev();
      loop {
        match next_value {
          Some(value) => {
            return Some(Entry::new(curr, value, self.query_version));
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
  }

  /// Returns the previous entry in the map.
  pub fn prev(&self) -> Option<Entry<'a, K, V, S, C>> {
    if S::ALWAYS_VALID {
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
    } else {
      let mut curr = self.ent.clone();
      let mut next_value = self.value.next();
      loop {
        match next_value {
          Some(value) => {
            return Some(Entry::new(curr, value, self.query_version));
          }
          None => {
            curr = curr.prev()?;
            next_value = curr.value().range(..=self.query_version).next();
          }
        }
      }
    }
  }
}
