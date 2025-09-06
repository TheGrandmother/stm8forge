#ifndef MIDI_H
#define MIDI_H

typedef enum  message_type  {
    M_INVALID                         = 0,
    M_NOTE_OFF                        = 0x80, // 2
    M_NOTE_ON                         = 0x90,// 2
    M_AFTERTOUCH                      = 0xa0,// 2
    M_CC                              = 0xb0,// 2
    M_PROGRAM_CHANGE                  = 0xc0,// 1
    M_CH_AFTERTOUCH                   = 0xd0,// 1
    M_PITCH_BEND                      = 0xe0,// 2
    M_SYSEX_START                     = 0xf0,
    M_QUARTER_FRAME                   = 0xf1, // 1
    M_SONG_POINTER                    = 0xf2, // 2
    M_SONG_SELECT                     = 0xf3, // 1
 // INVALID                         = 0xf4,
 // INVALID                         = 0xf5,
    M_TUNE_REQUEST                    = 0xf6,
    M_SYSEX_END                       = 0xf7, // Not supported
    M_CLOCK                           = 0xf8,
    M_MEASURE_END                     = 0xf9, // 1
    M_START                           = 0xfa,
    M_CONTINUE                        = 0xfb,
    M_STOP                            = 0xfc,
 // INVALID                         = 0xfd,
    M_ACTIVE_SENSE                    = 0xfe,
    M_RESET                           = 0xff,
} message_type ;

typedef struct {
    unsigned char ch;
    message_type type;
    unsigned char d1;
    unsigned char d2;
    unsigned char _length;
} MidiMessage;

message_type parse_type_byte(unsigned char b);

typedef enum  parser_state  {
  M_INIT,
  M_COMPLETE,
  M_D1,
  M_D2,
} parser_state;

parser_state parser(MidiMessage* m, parser_state s, unsigned char b);

#endif
