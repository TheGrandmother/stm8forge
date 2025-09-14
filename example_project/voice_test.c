#include "voice.h"
#include <forge.h>


void TEST_env_up_and_down() {
  test_start();
  ar_env e;
  init_env(&e);
  e.a = 10;
  e.d = 5;
  e.s = 10;
  e.r = 5;

  unsigned int old_val = e.val;
  set_gate(&e, 1);

  update_env(&e, 10);
  assert_gt(e.val, old_val);

  old_val = e.val;
  update_env(&e, 10);
  assert_gt(e.val, old_val);

  old_val = e.val;
  set_gate(&e, 0);
  update_env(&e, 10);
  assert_lt(e.val, old_val);

  old_val = e.val;
  set_gate(&e, 0);
  update_env(&e, 10);
  assert_lt(e.val, old_val);

  test_complete();
}

void TEST_tops_out_and_bottoms_out() {
  test_start();
  ar_env e;
  init_env(&e);
  e.a = 0xffff/3;
  e.s = 0xffff;
  e.r = 0xffff/3;
  set_gate(&e, 1);
  update_env(&e, 1);
  update_env(&e, 1);
  update_env(&e, 1);
  update_env(&e, 1);
  assert_eq(e.val, 0xffff);
  set_gate(&e, 0);
  update_env(&e, 1);
  update_env(&e, 1);
  update_env(&e, 1);
  update_env(&e, 1);
  assert_eq(e.val, 0);
  test_complete();
}

void TEST_note_to_c() {
  test_start();
  assert_eq(note_to_counter(0x3c), 0x3029);
  assert_eq(note_to_counter(0x3d), 0x2d75);
  assert_eq(note_to_counter(0x3c - 12), 0x3029 << 1);
  assert_eq(note_to_counter(0x3c + 12), 0x3029 >> 1);
  test_complete();
}

