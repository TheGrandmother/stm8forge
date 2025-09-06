#include "forge_test.h"
#include <stdio.h>

/*@
    logic integer _strlen(char str[], integer n) = (str[n] == 0) ? n : _strlen(str, n + 1);
    logic integer strlen(char str[]) = strlen(str);
    predicate is_string(char str[], integer max_len) = \exists integer i; 0 <= i < max_len && str[i] == '\0' ;
*/

enum test_status {
  FAILED =    0b00001,
  PASSED =    0b00010,
  COMPLETE =  0b00100,
  RUNNING =   0b01000,
  ASSERT =    0b10000
};


volatile unsigned char sif;

volatile enum test_status test_status = 0;
/*@
  global invariant exclusive_status:
  (test_status & FAILED) ==> !(test_status & PASSED) &&
  (test_status & PASSED) ==> !(test_status & FAILED);
*/

//@ logic integer message_length = 128;
#define message_length 128
char assert_message[message_length];




enum sif_command {
  DETECT_SIGN	        = '!',	// answer to detect command
  SIFCM_DETECT		= '_',	// command used to detect the interface
  SIFCM_COMMANDS	= 'i',	// get info about commands
  SIFCM_IFVER		= 'v',	// interface version
  SIFCM_SIMVER		= 'V',	// simulator version
  SIFCM_IFRESET		= '@',	// reset the interface
  SIFCM_CMDINFO		= 'I',	// info about a command
  SIFCM_CMDHELP		= 'h',	// help about a command
  SIFCM_STOP		= 's',	// stop simulation
  SIFCM_PRINT		= 'p',	// print character
  SIFCM_FIN_CHECK	= 'f',	// check input file for input
  SIFCM_READ		= 'r',	// read from input file
  SIFCM_WRITE		= 'w',	// write to output file
};

/*@
  assigns sif;
*/
void sif_stop(void) {
  sif= SIFCM_STOP;
}

/*@
  assigns sif;
*/
void sif_putchar(char c) {
  sif= SIFCM_PRINT;
  sif= c;
}

/*@
  assigns sif;
*/
void sif_print(char *s) {
  while (*s) {
    sif= SIFCM_PRINT;
    sif= *s++;
  }
}

/*@
  assigns sif;
*/
void sif_write(char *s) {
  while (*s) {
    sif= SIFCM_WRITE;
    sif= *s++;
  }
}


/*@
  requires \separated(
    message+(0..strlen(message)),
    name+(0..strlen(name)),
    assert_message+(0..message_length),
    &test_status
  );
  requires \valid(message+(0..strlen(message)));
  requires \valid(name+(0..strlen(name)));
  assigns assert_message[0..\min(strlen(message) + strlen(message), message_length)];
  assigns test_status;
*/
void _assert(char condition, char* message, int line, const char* name) {
  if (!condition) {
    if (test_status & RUNNING) {
      sprintf(assert_message, "%s:%d  %s", name, line, message);
      test_status |= (FAILED | ASSERT);
    } else {
      sif_print("assert: ");
      sif_print(name);
      sif_print(" ");
      sif_print(message);
      sif_putchar('\n');
      sif_stop();
    }
  }
}

void _assert_eq(int lhs, char* lhs_text, int rhs, char* rhs_text, int line, const char* name) {
  char buf[128];
  if (lhs !=  rhs) {
    sprintf(buf, "%s != %s (0x%x != 0x%x)", lhs_text, rhs_text, (unsigned int)lhs, (unsigned int)rhs);
    _test_assert(0, buf, line, name);
  }

}

/*@
  assigns assert_message[0..message_length-1];
  assigns test_status;
*/
void _test_assert(char condition, char* cond_text, int line, const char* name) {
  if (!condition) {
    sprintf(assert_message, "%s:%d  %s", name, line, cond_text);
    test_status |= FAILED;
  }
}


// Marks a test as completed
void test_complete(void) {
  test_status |= COMPLETE;
}




/*@
  requires \valid(assert_message+(0..message_length));
  assigns test_status;
  assigns assert_message[0];
  ensures test_status == RUNNING;
  ensures is_string(assert_message, message_length);
*/
void test_start(void) {
  assert_message[0] = '\0';
  test_status = RUNNING;
}
