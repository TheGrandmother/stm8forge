#include "stm8s.h"
#include "stm8s_conf.h"
#include "midi.h"
#include "main.h"
#include "voice.h"
#include <forge_test.h>
#include <stdio.h>

#define CONFIG_UNUSED_PINS_STM8S001 \
{ \
 GPIOA->DDR |= GPIO_PIN_2; \
 GPIOB->DDR |= GPIO_PIN_0 | GPIO_PIN_1 | GPIO_PIN_2 | GPIO_PIN_3 | GPIO_PIN_6 | GPIO_PIN_7; \
 GPIOC->DDR |= GPIO_PIN_1 | GPIO_PIN_2 | GPIO_PIN_7; \
 GPIOD->DDR |= GPIO_PIN_0 | GPIO_PIN_2 | GPIO_PIN_4 | GPIO_PIN_7;\
 GPIOE->DDR |= GPIO_PIN_5; \
 GPIOF->DDR |= GPIO_PIN_4; \
}



void debug_on() {
  GPIO_WriteLow(GPIOB, (GPIO_Pin_TypeDef)GPIO_PIN_5);
}

void debug_off() {
  GPIO_WriteHigh(GPIOB, (GPIO_Pin_TypeDef)GPIO_PIN_5);
}

void debug_flash() {
  char flashes = 10;
  while(flashes--) {
    long int d = 8000;
    debug_on();
    while (d--) {}
    debug_off();
    d = 8000;
    while (d--) {}
  }
}


static void TIM4_Config(void)
{

  TIM4_TimeBaseInit(TIM4_PRESCALER_128, 0xff);
  TIM4_ClearFlag(TIM4_FLAG_UPDATE);
  TIM4_SelectOnePulseMode(TIM4_OPMODE_REPETITIVE);

  TIM4_ITConfig(TIM4_IT_UPDATE, ENABLE);
  enableInterrupts();

  /* Enable TIM4 */

  TIM4_Cmd(ENABLE);
}


unsigned int tim2_max = 0xff;
void TIM2_Config(void) {
  TIM2_DeInit();
  TIM2_TimeBaseInit(TIM2_PRESCALER_1, tim2_max);
  TIM2_PrescalerConfig(TIM2_PRESCALER_1, TIM2_PSCRELOADMODE_IMMEDIATE);
  TIM2_OC3Init(TIM2_OCMODE_PWM1,
               TIM2_OUTPUTSTATE_ENABLE,
               tim2_max >> 1,
               TIM2_OCPOLARITY_HIGH
              );


  TIM2_OC3PreloadConfig(DISABLE);
  TIM2_ARRPreloadConfig(ENABLE);

  TIM2_Cmd(ENABLE);
}

volatile unsigned long wall_time = 0;

void increment_wall_time() {
  wall_time += 1;
}


static void TIM1_Config(void)
{

  TIM1_DeInit();

  TIM1_TimeBaseInit(TIM2_PRESCALER_64, TIM1_COUNTERMODE_UP, 0xFFFF, 0);

  /* Channel 1, 2,3 and 4 Configuration in PWM mode */

  TIM1_OC3Init(
    TIM1_OCMODE_PWM2,
    TIM1_OUTPUTSTATE_ENABLE,
    TIM1_OUTPUTNSTATE_ENABLE,
    0,
    TIM1_OCPOLARITY_LOW,
    TIM1_OCNPOLARITY_HIGH,
    TIM1_OCIDLESTATE_SET,
    TIM1_OCNIDLESTATE_RESET);

  /* TIM1 counter enable */
  TIM1_Cmd(ENABLE);

  /* TIM1 Main Output Enable */
  TIM1_CtrlPWMOutputs(ENABLE);
}



static void UART_Config(void)
{
  UART1_DeInit();
  UART1_Init((uint32_t)31250, UART1_WORDLENGTH_8D, UART1_STOPBITS_1, UART1_PARITY_NO,
             UART1_SYNCMODE_CLOCK_DISABLE, UART1_MODE_RX_ENABLE);

  /* Enable UART1 Half Duplex Mode*/
  UART1_Cmd(ENABLE);
}

void main(void)
{

#ifdef STM8S001
  CONFIG_UNUSED_PINS_STM8S001;
#endif

  GPIO_Init(GPIOB, (GPIO_Pin_TypeDef)GPIO_PIN_5, GPIO_MODE_OUT_OD_LOW_SLOW);

  debug_flash();

  CLK_DeInit();

  CLK_HSIPrescalerConfig(CLK_PRESCALER_HSIDIV1);
  CLK_SYSCLKConfig(CLK_PRESCALER_HSIDIV1);
  CLK_HSICmd(ENABLE);

  UART_Config();
  UART1_ReceiveData8();
  UART1_ClearFlag(UART1_FLAG_RXNE);

  TIM1_Config();
  TIM2_Config();
  TIM4_Config();


  midi_message m;
  init_message(&m);
  parser_state s = M_INIT;

  char buf[64] = "";

  sif_print("started\n");
  unsigned long time = TIM4_GetCounter();
  char key = 0xff;
  unsigned char duty = 0x80;


  ar_env env;
  init_env(&env);

  while (1)
  {

    if (wall_time != time) {
      unsigned char dt = wall_time - time;

      update_env(&env, dt << 1);

      TIM2_SetCompare3(0xff - (env.val >> 8));

      if (env.val <= 1) {
        TIM1_SetAutoreload(0);
        TIM1_SetCompare3(0);
      }
      time = wall_time;
    }

    if (UART1_GetFlagStatus(UART1_FLAG_RXNE) != RESET) {

      uint8_t b = UART1_ReceiveData8();
      UART1_ClearFlag(UART1_FLAG_RXNE);

      s = parser(&m, s, b);

      if (s == M_COMPLETE) {
        s = M_INIT;

        if (m.type == M_CC && m.d1 == 1) {
          duty = m.d2;
          uint16_t c = note_to_counter(key);
          TIM1_SetAutoreload(c);
          TIM1_SetCompare3(((unsigned long)duty*(c >> 1)) >> 7);
        }

        if (m.type == M_CC && m.d1 == 101) {
          set_a(&env, (unsigned int)m.d2 << 3);
        }

        if (m.type == M_CC && m.d1 == 102) {
          set_d(&env, (unsigned int)m.d2 << 3);
        }

        if (m.type == M_CC && m.d1 == 103) {
          set_s(&env, (unsigned int)m.d2 << 9);
        }

        if (m.type == M_CC && m.d1 == 104) {
          set_r(&env, (unsigned int)m.d2 << 3);
        }

        if (m.type == M_NOTE_ON && m.d2 != 0) {
          key = m.d1;
          set_gate(&env, 1);
          uint16_t c = note_to_counter(key);
          TIM1_SetAutoreload(c);
          TIM1_SetCompare3(((unsigned long)duty*(c >> 1)) >> 7);
        }

        if (m.type == M_NOTE_OFF && key == m.d1) {
          set_gate(&env, 0);
        }
      }

    }
  }
}
