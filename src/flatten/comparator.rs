use std::cmp;

use super::{Comparator, Equivalentor, QueryComparator, QueryEquivalentor};
use super::{Key, Query};

pub(super) struct MultipleVersionsComparator<C>(pub(super) C);

impl<C> From<C> for MultipleVersionsComparator<C> {
  fn from(comparator: C) -> Self {
    Self(comparator)
  }
}

impl<K, C> Equivalentor<Key<K>> for MultipleVersionsComparator<C>
where
  C: Equivalentor<K>,
{
  fn equivalent(&self, a: &Key<K>, b: &Key<K>) -> bool {
    a.version == b.version && self.0.equivalent(&a.key, &b.key)
  }
}

impl<K, C> Comparator<Key<K>> for MultipleVersionsComparator<C>
where
  C: Comparator<K>,
{
  fn compare(&self, a: &Key<K>, b: &Key<K>) -> cmp::Ordering {
    self
      .0
      .compare(&a.key, &b.key)
      .then_with(|| b.version.cmp(&a.version))
  }
}

impl<C, K, Q> QueryEquivalentor<Key<K>, Query<'_, Q, K>> for MultipleVersionsComparator<C>
where
  C: QueryEquivalentor<K, Q>,
  Q: ?Sized,
{
  fn query_equivalent(&self, a: &Key<K>, b: &Query<'_, Q, K>) -> bool {
    a.version == b.version && self.0.query_equivalent(&a.key, b.query)
  }
}

impl<C, K, Q> QueryComparator<Key<K>, Query<'_, Q, K>> for MultipleVersionsComparator<C>
where
  C: QueryComparator<K, Q>,
  Q: ?Sized,
{
  fn query_compare(&self, a: &Key<K>, b: &Query<'_, Q, K>) -> cmp::Ordering {
    self
      .0
      .query_compare(&a.key, b.query)
      .then_with(|| b.version.cmp(&a.version))
  }
}
