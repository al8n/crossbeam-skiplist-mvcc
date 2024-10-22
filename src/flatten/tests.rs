use crossbeam_skiplist::Comparable;

use super::{Key, Query, SkipMap};

#[test]
fn ord() {
  let query = Query::new(1, &3usize);
  let k = Key::new(3usize, 3);
  assert!(query.compare(&k).is_gt()); // larger version should be present before smaller version when key is the same.
}

#[test]
fn clone() {
  let map = SkipMap::new();
  map.insert(1, 1, 1).unwrap();
  let ent = map.get(1, &1);
  println!("{:?}", ent);
  let _ = ent.clone();

  let ent = map.get_versioned(1, &1);
  println!("{:?}", ent);
  let _ = ent.clone();
}
