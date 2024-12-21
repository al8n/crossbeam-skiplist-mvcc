use std::ops::Bound;

use crossbeam_skiplist_mvcc::nested::SkipMap;

#[test]
fn basic() {
  let map = SkipMap::new();
  map.insert(0, "key1", 1).unwrap();
  map.insert(0, "key3", 3).unwrap();
  map.insert(0, "key2", 2).unwrap();

  {
    let it = map.iter_all_versions(0);
    for (idx, ent) in it.enumerate() {
      assert_eq!(ent.version(), 0);
      assert_eq!(ent.key(), &format!("key{}", idx + 1));
      assert_eq!(ent.value().unwrap(), &(idx + 1));
    }
  }

  map.insert_unchecked(1, "a", 1);
  map.insert_unchecked(2, "a", 2);

  {
    let mut it = map.iter_all_versions(2);
    let ent = it.next().unwrap();
    assert_eq!(ent.version(), 2);
    assert_eq!(ent.key(), &"a");
    assert_eq!(ent.value().unwrap(), &2);

    let ent = it.next().unwrap();
    assert_eq!(ent.version(), 1);
    assert_eq!(ent.key(), &"a");
    assert_eq!(ent.value().unwrap(), &1);
  }

  map.insert_unchecked(2, "b", 2);
  map.insert_unchecked(1, "b", 1);

  {
    let mut it = map.range_all_versions(2, "b"..);

    let ent = it.next().unwrap();
    assert_eq!(ent.version(), 2);
    assert_eq!(ent.key(), &"b");
    assert_eq!(ent.value().unwrap(), &2);

    let ent = it.next().unwrap();
    assert_eq!(ent.version(), 1);
    assert_eq!(ent.key(), &"b");
    assert_eq!(ent.value().unwrap(), &1);
  }
}

#[test]
fn iter_all_versions_mvcc() {
  let map = SkipMap::new();
  map.insert_unchecked(1, "a", "a1");
  map.insert_unchecked(3, "a", "a2");
  map.insert_unchecked(1, "c", "c1");
  map.insert_unchecked(3, "c", "c2");

  let mut it = map.iter_all_versions(0);
  let mut num = 0;
  while it.next().is_some() {
    num += 1;
  }

  assert_eq!(num, 0);

  let mut it = map.iter_all_versions(1);
  let a1 = it.next().unwrap();
  assert_eq!(a1.version(), 1);
  assert_eq!(a1.key(), &"a");
  assert_eq!(a1.value().unwrap(), &"a1");

  let c1 = it.next().unwrap();
  assert_eq!(c1.version(), 1);
  assert_eq!(c1.key(), &"c");
  assert_eq!(c1.value().unwrap(), &"c1");

  let mut it = map.iter_all_versions(2);
  let a1 = it.next().unwrap();
  assert_eq!(a1.version(), 1);
  assert_eq!(a1.key(), &"a");
  assert_eq!(a1.value().unwrap(), &"a1");

  let c1 = it.next().unwrap();
  assert_eq!(c1.version(), 1);
  assert_eq!(c1.key(), &"c");
  assert_eq!(c1.value().unwrap(), &"c1");

  let mut it = map.iter_all_versions(3);
  let a2 = it.next().unwrap();
  assert_eq!(a2.version(), 3);
  assert_eq!(a2.key(), &"a");
  assert_eq!(a2.value().unwrap(), &"a2");

  let a1 = it.next().unwrap();
  assert_eq!(a1.version(), 1);
  assert_eq!(a1.key(), &"a");
  assert_eq!(a1.value().unwrap(), &"a1");

  let c2 = it.next().unwrap();
  assert_eq!(c2.version(), 3);
  assert_eq!(c2.key(), &"c");
  assert_eq!(c2.value().unwrap(), &"c2");

  let c1 = it.next().unwrap();
  assert_eq!(c1.version(), 1);
  assert_eq!(c1.key(), &"c");
  assert_eq!(c1.value().unwrap(), &"c1");
}

#[test]
fn get_mvcc() {
  let map = SkipMap::new();
  map.insert_unchecked(1, "a", "a1");
  map.insert_unchecked(3, "a", "a2");
  map.insert_unchecked(1, "c", "c1");
  map.insert_unchecked(3, "c", "c2");

  let ent = map.get(1, "a").unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a1");

  let ent = map.get(2, "a").unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a1");

  let ent = map.get(3, "a").unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a2");

  let ent = map.get(4, "a").unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a2");

  assert!(map.get(0, "b").is_none());
  assert!(map.get(1, "b").is_none());
  assert!(map.get(2, "b").is_none());
  assert!(map.get(3, "b").is_none());
  assert!(map.get(4, "b").is_none());

  let ent = map.get(1, "c").unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c1");

  let ent = map.get(2, "c").unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c1");

  let ent = map.get(3, "c").unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c2");

  let ent = map.get(4, "c").unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c2");

  assert!(map.get(5, "d").is_none());
}

#[test]
fn gt() {
  let map = SkipMap::new();
  map.insert_unchecked(1, "a", "a1");
  map.insert_unchecked(3, "a", "a2");
  map.insert_unchecked(1, "c", "c1");
  map.insert_unchecked(3, "c", "c2");
  map.insert_unchecked(5, "c", "c3");

  let ent = map.lower_bound(1, Bound::Excluded("")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a1");

  let ent = map.lower_bound(2, Bound::Excluded("")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a1");

  let ent = map.lower_bound(3, Bound::Excluded("")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a2");

  let ent = map.lower_bound(1, Bound::Excluded("a")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c1");

  let ent = map.lower_bound(2, Bound::Excluded("a")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c1");

  let ent = map.lower_bound(3, Bound::Excluded("a")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c2");

  let ent = map.lower_bound(1, Bound::Excluded("b")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c1");

  let ent = map.lower_bound(2, Bound::Excluded("b")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c1");

  let ent = map.lower_bound(3, Bound::Excluded("b")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c2");

  let ent = map.lower_bound(4, Bound::Excluded("b")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c2");

  let ent = map.lower_bound(5, Bound::Excluded("b")).unwrap();
  assert_eq!(ent.version(), 5);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c3");

  let ent = map.lower_bound(6, Bound::Excluded("b")).unwrap();
  assert_eq!(ent.version(), 5);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c3");

  assert!(map.lower_bound(1, Bound::Excluded("c")).is_none());
  assert!(map.lower_bound(2, Bound::Excluded("c")).is_none());
  assert!(map.lower_bound(3, Bound::Excluded("c")).is_none());
  assert!(map.lower_bound(4, Bound::Excluded("c")).is_none());
  assert!(map.lower_bound(5, Bound::Excluded("c")).is_none());
  assert!(map.lower_bound(6, Bound::Excluded("c")).is_none());
}

#[test]
fn ge() {
  let map = SkipMap::new();
  map.insert_unchecked(1, "a", "a1");
  map.insert_unchecked(3, "a", "a2");
  map.insert_unchecked(1, "c", "c1");
  map.insert_unchecked(3, "c", "c2");

  assert!(map.lower_bound(0, Bound::Included("a")).is_none());
  assert!(map.lower_bound(0, Bound::Included("b")).is_none());
  assert!(map.lower_bound(0, Bound::Included("c")).is_none());

  let ent = map.lower_bound(1, Bound::Included("a")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a1");

  let ent = map.lower_bound(2, Bound::Included("a")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a1");

  let ent = map.lower_bound(3, Bound::Included("a")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a2");

  let ent = map.lower_bound(4, Bound::Included("a")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a2");

  let ent = map.lower_bound(1, Bound::Included("b")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c1");

  let ent = map.lower_bound(2, Bound::Included("b")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c1");

  let ent = map.lower_bound(3, Bound::Included("b")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c2");

  let ent = map.lower_bound(4, Bound::Included("b")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c2");

  let ent = map.lower_bound(1, Bound::Included("c")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c1");

  let ent = map.lower_bound(2, Bound::Included("c")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c1");

  let ent = map.lower_bound(3, Bound::Included("c")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c2");

  let ent = map.lower_bound(4, Bound::Included("c")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c2");

  assert!(map.lower_bound(0, Bound::Included("d")).is_none());
  assert!(map.lower_bound(1, Bound::Included("d")).is_none());
  assert!(map.lower_bound(2, Bound::Included("d")).is_none());
  assert!(map.lower_bound(3, Bound::Included("d")).is_none());
  assert!(map.lower_bound(4, Bound::Included("d")).is_none());
}

#[test]
fn le() {
  let map = SkipMap::new();
  map.insert_unchecked(1, "a", "a1");
  map.insert_unchecked(3, "a", "a2");
  map.insert_unchecked(1, "c", "c1");
  map.insert_unchecked(3, "c", "c2");

  assert!(map.upper_bound(0, Bound::Included("a")).is_none());
  assert!(map.upper_bound(0, Bound::Included("b")).is_none());
  assert!(map.upper_bound(0, Bound::Included("c")).is_none());

  let ent = map.upper_bound(1, Bound::Included("a")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a1");

  let ent = map.upper_bound(2, Bound::Included("a")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a1");

  let ent = map.upper_bound(3, Bound::Included("a")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a2");

  let ent = map.upper_bound(4, Bound::Included("a")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a2");

  let ent = map.upper_bound(1, Bound::Included("b")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a1");

  let ent = map.upper_bound(2, Bound::Included("b")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a1");

  let ent = map.upper_bound(3, Bound::Included("b")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a2");

  let ent = map.upper_bound(4, Bound::Included("b")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a2");

  let ent = map.upper_bound(1, Bound::Included("c")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c1");

  let ent = map.upper_bound(2, Bound::Included("c")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c1");

  let ent = map.upper_bound(3, Bound::Included("c")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c2");

  let ent = map.upper_bound(4, Bound::Included("c")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c2");

  let ent = map.upper_bound(1, Bound::Included("d")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c1");

  let ent = map.upper_bound(2, Bound::Included("d")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c1");

  let ent = map.upper_bound(3, Bound::Included("d")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c2");

  let ent = map.upper_bound(4, Bound::Included("d")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c2");
}

#[test]
fn lt() {
  let map = SkipMap::new();

  map.insert_unchecked(1, "a", "a1");
  map.insert_unchecked(3, "a", "a2");
  map.insert_unchecked(1, "c", "c1");
  map.insert_unchecked(3, "c", "c2");

  assert!(map.upper_bound(0, Bound::Excluded("a")).is_none());
  assert!(map.upper_bound(0, Bound::Excluded("b")).is_none());
  assert!(map.upper_bound(0, Bound::Excluded("c")).is_none());
  assert!(map.upper_bound(1, Bound::Excluded("a")).is_none());
  assert!(map.upper_bound(2, Bound::Excluded("a")).is_none());

  let ent = map.upper_bound(1, Bound::Excluded("b")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a1");

  let ent = map.upper_bound(2, Bound::Excluded("b")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a1");

  let ent = map.upper_bound(3, Bound::Excluded("b")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a2");

  let ent = map.upper_bound(4, Bound::Excluded("b")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a2");

  let ent = map.upper_bound(1, Bound::Excluded("c")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a1");

  let ent = map.upper_bound(2, Bound::Excluded("c")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a1");

  let ent = map.upper_bound(3, Bound::Excluded("c")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a2");

  let ent = map.upper_bound(4, Bound::Excluded("c")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"a");
  assert_eq!(ent.value(), &"a2");

  let ent = map.upper_bound(1, Bound::Excluded("d")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c1");

  let ent = map.upper_bound(2, Bound::Excluded("d")).unwrap();
  assert_eq!(ent.version(), 1);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c1");

  let ent = map.upper_bound(3, Bound::Excluded("d")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c2");

  let ent = map.upper_bound(4, Bound::Excluded("d")).unwrap();
  assert_eq!(ent.version(), 3);
  assert_eq!(ent.key(), &"c");
  assert_eq!(ent.value(), &"c2");
}

#[test]
fn all_versions_iter_forwards() {
  const N: usize = 100;

  let map = SkipMap::new();
  for i in 0..N {
    map.insert_unchecked(0, i, i);
    map.remove(1, i).unwrap();
  }

  let it = map.iter_all_versions(0);
  let mut i = 0;
  for entry in it {
    assert_eq!(entry.version(), 0);
    assert_eq!(entry.key(), &i);
    assert_eq!(entry.value().unwrap(), &i);
    i += 1;
  }

  assert_eq!(i, N);

  let it = map.iter_all_versions(1);

  let mut i = 0;
  for entry in it {
    if i % 2 == 1 {
      assert_eq!(entry.version(), 0);
      assert_eq!(*entry.key(), i / 2);
      assert_eq!(entry.value().unwrap(), &(i / 2));
    } else {
      assert_eq!(entry.version(), 1);
      assert_eq!(*entry.key(), i / 2);
      assert!(entry.value().is_none());
    }

    i += 1;
  }

  assert_eq!(i, 2 * N);

  let mut it = map.iter(1);
  assert!(it.next().is_none());
}

#[test]
fn all_versions_iter_backwards() {
  const N: usize = 100;

  let map = SkipMap::new();
  for i in 0..N {
    map.insert_unchecked(0, i, i);
    map.remove_unchecked(1, i);
  }

  let it = map.iter_all_versions(0).rev();
  let mut i = 0;
  for entry in it {
    i += 1;
    assert_eq!(*entry.key(), N - i);
    assert_eq!(*entry.value().unwrap(), N - i);
  }
  assert_eq!(i, N);

  let it = map.iter_all_versions(1).rev();
  let mut i = 0;
  for ref entry in it {
    if i % 2 == 0 {
      assert_eq!(entry.version(), 0);
      assert_eq!(*entry.key(), N - 1 - i / 2);
      assert_eq!(*entry.value().unwrap(), N - 1 - i / 2);
    } else {
      assert_eq!(entry.version(), 1);
      assert_eq!(*entry.key(), N - 1 - i / 2);
      assert!(entry.value().is_none());
    }
    i += 1;
  }
  assert_eq!(i, 2 * N);

  let mut it = map.iter(1);
  assert!(it.next().is_none());
}

#[test]
fn cursor_forwards() {
  const N: usize = 100;

  let map = SkipMap::new();
  for i in 0..N {
    map.insert_unchecked(0, i, i);
    map.remove_unchecked(1, i);
  }

  let mut ent = map.front(0);
  let mut i = 0;
  while let Some(entry) = ent {
    assert_eq!(entry.key(), &i);
    assert_eq!(entry.value(), &i);
    i += 1;
    ent = entry.next();
  }
  assert_eq!(i, N);

  let mut ent = map.front_with_tombstone(1);
  let mut i = 0;

  while let Some(ref entry) = ent {
    if i % 2 == 1 {
      assert_eq!(entry.version(), 0);
      assert_eq!(*entry.key(), i / 2);
      assert_eq!(*entry.value().unwrap(), i / 2);
    } else {
      assert_eq!(entry.version(), 1);
      assert_eq!(*entry.key(), i / 2);
      assert!(entry.value().is_none(), "{:?}", entry.value());
    }

    ent = entry.next();
    i += 1;
  }
  assert_eq!(i, 2 * N);
  let ent = map.front(1);
  assert!(ent.is_none());
}

#[test]
fn cursor_backwards() {
  const N: usize = 100;

  let map = SkipMap::new();
  for i in 0..N {
    map.insert_unchecked(0, i, i);
    map.remove_unchecked(1, i);
  }

  let mut ent = map.back(0);
  let mut i = 0;
  while let Some(entry) = ent {
    i += 1;
    assert_eq!(*entry.key(), N - i);
    assert_eq!(*entry.value(), N - i);
    ent = entry.prev();
  }
  assert_eq!(i, N);

  let mut ent = map.back_with_tombstone(1);
  let mut i = 0;
  while let Some(ref entry) = ent {
    if i % 2 == 0 {
      assert_eq!(entry.version(), 0);
      assert_eq!(*entry.key(), N - 1 - i / 2);
      assert_eq!(*entry.value().unwrap(), N - 1 - i / 2);
    } else {
      assert_eq!(entry.version(), 1);
      assert_eq!(*entry.key(), N - 1 - i / 2);
      assert!(entry.value().is_none());
    }
    i += 1;
    ent = entry.prev();
  }
  assert_eq!(i, 2 * N);
  let ent = map.back(1);
  assert!(ent.is_none());
}

#[test]
fn range_forwards() {
  const N: usize = 100;

  let map = SkipMap::new();
  for i in 0..N {
    map.insert_unchecked(0, i, i);
    map.remove_unchecked(1, i);
  }

  let it = map.range(0, ..=50);
  let mut i = 0;
  for entry in it {
    assert_eq!(entry.key(), &i);
    assert_eq!(entry.value(), &i);
    i += 1;
  }

  assert_eq!(i, 51);

  let it = map.range_all_versions(1, ..=50);
  let mut i = 0;

  for entry in it {
    if i % 2 == 1 {
      assert_eq!(entry.version(), 0);
      assert_eq!(*entry.key(), i / 2);
      assert_eq!(*entry.value().unwrap(), i / 2);
    } else {
      assert_eq!(entry.version(), 1);
      assert_eq!(*entry.key(), i / 2);
      assert!(entry.value().is_none());
    }

    i += 1;
  }

  assert_eq!(i, 102);

  let mut it = map.range(1, ..=50);
  assert!(it.next().is_none());
}

#[test]
fn range_backwards() {
  const N: usize = 100;

  let map = SkipMap::new();
  for i in 0..N {
    map.insert_unchecked(0, i, i);
    map.remove_unchecked(1, i);
  }

  let it = map.range(0, ..=50).rev();
  let mut i = 0;
  for entry in it {
    i += 1;
    assert_eq!(*entry.key(), 51 - i);
    assert_eq!(*entry.value(), 51 - i);
  }
  assert_eq!(i, 51);

  let it = map.range_all_versions(1, ..=50).rev();
  let mut i = 0;
  for ref entry in it {
    if i % 2 == 0 {
      assert_eq!(entry.version(), 0);
      assert_eq!(*entry.key(), 51 - 1 - i / 2);
      assert_eq!(*entry.value().unwrap(), 51 - 1 - i / 2);
    } else {
      assert_eq!(entry.version(), 1);
      assert_eq!(*entry.key(), 51 - 1 - i / 2);
      assert!(entry.value().is_none());
    }
    i += 1;
  }
  assert_eq!(i, 102);

  let mut it = map.range(1, ..=50);
  assert!(it.next().is_none());
}

#[test]
fn iter_latest() {
  const N: usize = 100;

  let map = SkipMap::new();
  for i in 0..N {
    map.insert_unchecked(0, i, i);
  }

  for i in 50..N {
    map.insert_unchecked(1, i, i + 1000);
  }

  for i in 0..50 {
    map.insert_unchecked(2, i, i + 1000);
  }

  let mut it = map.iter(4);
  let mut num = 0;

  for i in 0..N {
    let ent = it.next().unwrap();
    if i < 50 {
      assert_eq!(ent.version(), 2);
    } else {
      assert_eq!(ent.version(), 1);
    }
    assert_eq!(ent.key(), &i);
    assert_eq!(ent.value(), &(i + 1000));
    num += 1;
  }

  assert_eq!(num, N);
}

#[test]
fn range_latest() {
  const N: usize = 100;

  let map = SkipMap::new();
  for i in 0..N {
    map.insert_unchecked(0, i, i);
  }

  for i in 50..N {
    map.insert_unchecked(1, i, i + 1000);
  }

  for i in 0..50 {
    map.insert_unchecked(2, i, i + 1000);
  }

  let mut it = map.range::<usize, _>(4, ..);

  let mut num = 0;
  for i in 0..N {
    let ent = it.next().unwrap();
    if i < 50 {
      assert_eq!(ent.version(), 2);
    } else {
      assert_eq!(ent.version(), 1);
    }
    assert_eq!(ent.key(), &i);
    assert_eq!(ent.value(), &(i + 1000));
    num += 1;
  }

  assert_eq!(num, N);
}

#[test]
fn compact() {
  let map = SkipMap::new();

  map.insert_unchecked(1, "a", "a1");
  map.insert_unchecked(3, "a", "a2");
  map.insert_unchecked(1, "c", "c1");
  map.insert_unchecked(3, "c", "c2");

  let version = map.compact(2);
  assert_eq!(version, 2);

  for ent in map.iter_all_versions(3) {
    assert_eq!(ent.version(), 3);
  }
}
