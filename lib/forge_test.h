#ifndef FORGE_TEST_H
#define FORGE_TEST_H

/*@
  terminates \true;
  exits \true;
  assigns \nothing;
*/
void _assert(char condition, char* message, int line, const char* name);
#define assert(condition, message) _assert(condition, message, __LINE__, __func__)

void _test_assert(char condition, char* cond_text, int line, const char* name);
#define test_assert(condition) _test_assert(condition, #condition, __LINE__, __func__)


void _assert_eq(int lhs, char* lhs_text, int rhs, char* rhs_text, int line, const char* name);
#define assert_eq(lhs, rhs) _assert_eq((int)lhs, #lhs, (int)rhs, #rhs, __LINE__, __func__)

void test_complete(void);
void test_start(void);

#endif
