use core::fmt::Debug;

use crossbeam_skiplist::{equivalentor::Comparator, map};
use dbutils::state::State;
use snapshotor::{CursorExt, DoubleEndedCursorExt, Entry as _, NoopValidator};

use crate::{sealed::TombstoneValidator, Transfer};

use super::{comparator::MultipleVersionsComparator, Key};

pub struct MapEntry<'a, K, V, C>(
  pub(super) map::Entry<'a, Key<K>, Option<V>, MultipleVersionsComparator<C>>,
);

impl<'a, K, V, C> From<map::Entry<'a, Key<K>, Option<V>, MultipleVersionsComparator<C>>>
  for MapEntry<'a, K, V, C>
{
  #[inline]
  fn from(src: map::Entry<'a, Key<K>, Option<V>, MultipleVersionsComparator<C>>) -> Self {
    Self(src)
  }
}

impl<K, V, C> Clone for MapEntry<'_, K, V, C> {
  #[inline]
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<K, V, C> snapshotor::Entry for MapEntry<'_, K, V, C> {
  type Key = K;
  type Value = Option<V>;
  type Version = u64;

  #[inline]
  fn key(&self) -> &Self::Key {
    &self.0.key().key
  }

  #[inline]
  fn value(&self) -> &Self::Value {
    self.0.value()
  }

  #[inline]
  fn version(&self) -> Self::Version {
    self.0.key().version
  }
}

impl<K, V, C> snapshotor::Cursor for MapEntry<'_, K, V, C>
where
  C: Comparator<K>,
{
  fn next(&self) -> Option<Self>
  where
    Self: Sized,
  {
    self.0.next().map(MapEntry)
  }
}

impl<K, V, C> snapshotor::DoubleEndedCursor for MapEntry<'_, K, V, C>
where
  C: Comparator<K>,
{
  fn next_back(&self) -> Option<Self>
  where
    Self: Sized,
  {
    self.0.prev().map(MapEntry)
  }
}

/// A reference-counted entry in a map.
pub struct Entry<'a, K, V, S, C> {
  pub(super) ent: MapEntry<'a, K, V, C>,
  query_version: u64,
  _m: core::marker::PhantomData<S>,
}

impl<'a, K: Debug, V: Debug, C, S> Debug for Entry<'a, K, V, S, C>
where
  S: Transfer<'a, V>,
  S::To: Debug,
  K: Debug,
  V: Debug,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("Entry")
      .field("version", &self.version())
      .field("key", &self.key())
      .field("value", &self.value())
      .finish()
  }
}

impl<K, V, S, C> Clone for Entry<'_, K, V, S, C> {
  #[inline]
  fn clone(&self) -> Self {
    Self {
      ent: self.ent.clone(),
      query_version: self.query_version,
      _m: core::marker::PhantomData,
    }
  }
}

impl<'a, K, V, S, C> Entry<'a, K, V, S, C> {
  /// Returns the version of the entry.
  #[inline]
  pub fn version(&self) -> u64 {
    self.ent.version()
  }

  /// Returns the key of the entry.
  #[inline]
  pub fn key(&self) -> &'a K {
    &self.ent.0.key().key
  }

  /// Returns the value of the entry.
  #[inline]
  pub fn value(&self) -> S::To
  where
    S: Transfer<'a, V>,
  {
    S::output(self.ent.0.value().as_ref())
  }

  /// Returns a reference to the comparator.
  #[inline]
  pub fn comparator(&self) -> &'a C {
    &self.ent.0.comparator().0
  }

  #[inline]
  pub(super) fn new(entry: MapEntry<'a, K, V, C>, query_version: u64) -> Self {
    Self {
      ent: entry,
      query_version,
      _m: core::marker::PhantomData,
    }
  }
}

impl<K, V, S, C> Entry<'_, K, V, S, C>
where
  S: State,
  C: Comparator<K>,
{
  /// Returns the next entry in the map.
  pub fn next(&self) -> Option<Self> {
    if !S::ALWAYS_VALID {
      let mut curr = self.ent.0.next();
      loop {
        match curr {
          None => return None,
          Some(ent) => {
            let curr_key = ent.key();
            if curr_key.version > self.query_version {
              curr = ent.next();
              continue;
            }
            break Some(MapEntry(ent));
          }
        }
      }
    } else {
      self.ent.next_dedup(
        &self.query_version,
        &self.ent.0.comparator().0,
        &NoopValidator,
        &TombstoneValidator,
      )
    }
    .map(|ent| Entry::new(ent, self.query_version))
  }

  /// Returns the previous entry in the map.
  pub fn prev(&self) -> Option<Self> {
    if !S::ALWAYS_VALID {
      let mut curr = self.ent.0.prev();
      loop {
        match curr {
          None => return None,
          Some(ent) => {
            let curr_key = ent.key();
            if curr_key.version > self.query_version {
              curr = ent.prev();
              continue;
            }
            break Some(MapEntry(ent));
          }
        }
      }
    } else {
      self.ent.next_back_dedup(
        &self.query_version,
        &self.ent.0.comparator().0,
        &NoopValidator,
        &TombstoneValidator,
      )
    }
    .map(|ent| Entry::new(ent, self.query_version))
  }
}
