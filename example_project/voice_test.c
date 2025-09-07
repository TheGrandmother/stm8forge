#include "voice.h"
#include <forge_test.h>


void TEST_env_up_and_down() {
  test_start();
  ar_env e;
  init_env(&e);
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

void TEST_hold_has_effect() {
  test_start();
  ar_env e;
  init_env(&e);
  e.a = 0xffff/3;
  e.r = 0xffff/3;
  e.hold = 0;
  set_gate(&e, 1);
  update_env(&e, 1);
  update_env(&e, 1);
  update_env(&e, 1);
  assert_eq(e.gate, 0);
  update_env(&e, 1);
  assert_lt(e.val, 0xffff);
  test_complete();
}

void TEST_vel_to_duty() {
  test_start();
  assert_eq(vel_to_duty(0x00, 0xB0B), 1);
  assert_lt(vel_to_duty(0x7f / 3, 0xB0B), 0xB0B >> 1);
  assert_gt(vel_to_duty(2*(0x7f / 3), 0xB0B), 0xB0B >> 1);
  test_complete();
}
void TEST_note_to_c() {
  test_start();
  assert_eq(note_to_counter(0x3c), 0x1ddc);
  assert_eq(note_to_counter(0x3d), 0x1c2f);
  assert_eq(note_to_counter(0x3c - 12), 0x1ddc << 1);
  assert_eq(note_to_counter(0x3c + 12), 0x1ddc >> 1);
  test_complete();
}

