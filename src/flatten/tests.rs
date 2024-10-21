use crossbeam_skiplist::Comparable;

use super::{Key, Query};

#[test]
fn ord() {
  let query = Query::new(1, &3usize);
  let k = Key::new(3usize, 3);
  assert!(query.compare(&k).is_gt()); // larger version should be present before smaller version when key is the same.
}
