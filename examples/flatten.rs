use crossbeam_skiplist_mvcc::flatten::SkipMap;

fn main() {
  let map = SkipMap::new();
  map.insert(0, "key1", 1).unwrap();
  map.insert(0, "key3", 3).unwrap();
  map.insert(0, "key2", 2).unwrap();

  {
    let it = map.iter_all(0);
    for (idx, ent) in it.enumerate() {
      assert_eq!(ent.version(), 0);
      assert_eq!(ent.key(), &format!("key{}", idx + 1));
      assert_eq!(ent.value().unwrap(), &(idx + 1));
    }
  }

  map.insert_unchecked(1, "a", 1);
  map.insert_unchecked(2, "a", 2);

  {
    let mut it = map.iter_all(2);
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
    let mut it = map.range_all(2, "b"..);

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
