#include "voice.h"


void update_env(ar_env* e, unsigned int dt) {
  if (e->gate) {
    unsigned int dv = (e->a)*dt;
    if (e->val >= 0xffff - dv) {
      e->val = 0xffff;
      if (!e->hold) {
        e->gate = 0;
      }
    } else {
      e->val += dv;
    }
  } else {
    unsigned int dv = (e->r)*dt;
    if (e->val <= 0 + dv) {
      e->val = 0;
    } else {
      e->val -= dv;
    }
  }
}

void set_gate(ar_env* e, unsigned char gate) {
  e->gate = gate;
}

void init_env(ar_env* e) {
  e->gate = 0;
  e->hold = 1;
  e->val = 0;
  e->t = 0;
  e->a = 0xffff/5000;
  e->r = 0xffff/10000;
}

unsigned int vel_to_duty(char vel, unsigned int max) {
  if (vel == 0) {
    return 1;
  }
  return ((long)vel * (long)max) / 0x7f;
}

unsigned int counters[12] = {
  0x1ddc, // counter at middle C aka MIDI note 60/0x3c
  0x1c2f,
  0x1a9a,
  0x191c,
  0x17b3,
  0x165e,
  0x151d,
  0x13ee,
  0x12cf,
  0x11c1,
  0x10c2,
  0x0fd1  // Middle B
};

unsigned int note_to_counter(char note) {
  unsigned char deg = note % 12;
  char oct = note / 12;
  if (oct > 5) {
    return counters[deg] >> (oct-5);
  } else {
    return counters[deg] << (5-oct);
  }
}
