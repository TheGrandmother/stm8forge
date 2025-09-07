#include "stm8s.h"
#include "stm8s_conf.h"
#include "midi.h"
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

  // Each counter will correspond to 2ms
  TIM4_TimeBaseInit(TIM4_PRESCALER_128, 0xff);
  TIM4_ClearFlag(TIM4_FLAG_UPDATE);
  TIM4_SelectOnePulseMode(TIM4_OPMODE_REPETITIVE);

  // TIM4_ITConfig(TIM4_IT_UPDATE, ENABLE);
  // enableInterrupts();

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

unsigned char channel = 0;


unsigned int tim1_max = 0xFFFF >> 5;
static void TIM1_Config(void)
{

  TIM1_DeInit();

  TIM1_TimeBaseInit(TIM2_PRESCALER_4, TIM1_COUNTERMODE_UP, tim1_max, 0);

  /* Channel 1, 2,3 and 4 Configuration in PWM mode */

  TIM1_OC3Init(
    TIM1_OCMODE_PWM2,
    TIM1_OUTPUTSTATE_ENABLE,
    TIM1_OUTPUTNSTATE_ENABLE,
    tim1_max >> 1,
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
  uint8_t time = TIM4_GetCounter();
  char key = 0xff;


  ar_env env;
  init_env(&env);


  while (1)
  {

    if (TIM4_GetCounter() != time) {
      unsigned char new_time = TIM4_GetCounter();
      unsigned char dt = new_time - time;
      if (new_time < time) {
        dt = new_time + (0xff - time);
      }
      update_env(&env, dt >> 1); // Counts in 2ms increments
      TIM2_SetCompare3(0xff - (env.val >> 8) + 2);
      time=new_time;
    }

    if (UART1_GetFlagStatus(UART1_FLAG_RXNE) != RESET) {

      uint8_t b = UART1_ReceiveData8();
      UART1_ClearFlag(UART1_FLAG_RXNE);

      s = parser(&m, s, b);
      // sprintf(buf, "%x\n", s);
      // sif_print(buf);

      if (s == M_COMPLETE) {
        s = M_INIT;
        if (m.ch == channel) {
          if (m.type == M_NOTE_ON) {
            GPIO_WriteReverse(GPIOB, (GPIO_Pin_TypeDef)GPIO_PIN_5);
            key = m.d1;
            set_gate(&env, 1);
            uint16_t c = note_to_counter(m.d1);
            TIM1_SetAutoreload(c);
            TIM1_SetCompare3(c >> 1);
          }

          if (m.type == M_NOTE_OFF && key == m.d1) {
            set_gate(&env, 0);
          }
        }
      }

    }
  }
}
