#ifndef FORGE_TEST_H
#define FORGE_TEST_H


void sif_print(char *s);

void _assert(char condition, char* message, int line, const char* name);
#define assert(condition, message) _assert(condition, message, __LINE__, __func__)

void _test_assert(char condition, char* cond_text, int line, const char* name);
#define test_assert(condition) _test_assert(condition, #condition, __LINE__, __func__)


void _assert_eq(int lhs, char* lhs_text, int rhs, char* rhs_text, int line, const char* name);
#define assert_eq(lhs, rhs) _assert_eq((int)lhs, #lhs, (int)rhs, #rhs, __LINE__, __func__)

void _assert_gt(int lhs, char* lhs_text, int rhs, char* rhs_text, int line, const char* name);
#define assert_gt(lhs, rhs) _assert_gt((int)lhs, #lhs, (int)rhs, #rhs, __LINE__, __func__)


void _assert_gte(int lhs, char* lhs_text, int rhs, char* rhs_text, int line, const char* name);
#define assert_gte(lhs, rhs) _assert_gt((int)lhs, #lhs, (int)rhs, #rhs, __LINE__, __func__)

void _assert_lt(int lhs, char* lhs_text, int rhs, char* rhs_text, int line, const char* name);
#define assert_lt(lhs, rhs) _assert_lt((int)lhs, #lhs, (int)rhs, #rhs, __LINE__, __func__)

void _assert_lte(int lhs, char* lhs_text, int rhs, char* rhs_text, int line, const char* name);
#define assert_lte(lhs, rhs) _assert_lte((int)lhs, #lhs, (int)rhs, #rhs, __LINE__, __func__)

void test_complete(void);
void test_start(void);

#endif
