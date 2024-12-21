use super::SkipMap;

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
