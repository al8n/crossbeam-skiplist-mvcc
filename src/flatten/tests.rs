use crossbeam_skiplist::equivalent::Comparable;

use super::{Key, Query, SkipMap};

#[test]
fn ord() {
  let query = Query::new(1, &3usize);
  let k = Key::new(3usize, 3);
  assert!(k.compare(&query).is_lt()); // larger version should be present before smaller version when key is the same.
}

#[test]
fn clone() {
  let map = SkipMap::new();
  map.insert(1, 1, 1).unwrap();
  let ent = map.get(1, &1);
  println!("{:?}", ent);
  let _ = ent.clone();

  let ent = map.get_with_tombstone(1, &1);
  println!("{:?}", ent);
  let _ = ent.clone();
}
