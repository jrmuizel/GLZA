/***********************************************************************

Copyright 2014-2015 Kennon Conrad

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

***********************************************************************/

// GLZAdecode.c
//   Decodes files created by GLZA1encode
//
// Usage:
//   GLZAdecode [-t#] <infilename> <outfilename>, where # is 1 or 2 and is the number of threads

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <pthread.h>
#define decode
const unsigned char CAP_CHAR = 0x43;
const unsigned int START_UTF8_2BYTE_symbols = 0x80;
const unsigned int START_UTF8_3BYTE_symbols = 0x800;
const unsigned int START_UTF8_4BYTE_symbols = 0x10000;
const unsigned int MAX_INSTANCES_FOR_MTF_QUEUE = 15;
const unsigned int MTF_QUEUE_SIZE = 64;
const unsigned int CHARS_TO_WRITE = 1000000;
const unsigned int MAX_SYMBOLS_DEFINED = 0x00C00000;
const unsigned int INITIAL_LIST_SIZE = 0x800;
const unsigned int BIG_LIST_SIZE = 0x400000;

unsigned char out_char0[12000000], out_char1[12000000];
unsigned char mtf_queue_miss_code_length[16], mtf_queue_size[16], mtf_queue_offset[16];
unsigned char symbol_strings[500000000], new_symbol_string[0x00C00000];
unsigned char lookup_bits[0x100][0x1000];
unsigned char symbol_count, num_threads, max_code_length, max_regular_code_length, find_first_symbol, end_symbol;
unsigned char UTF8_compliant, base_bits, cap_encoded, use_mtf, caps_on, prior_is_cap, write_caps_on, delta_gap, delta_on;
unsigned char out_buffer_num, out_buffers_sent, prior_end;
unsigned char bin_bits_under_max[0x100];
unsigned char *symbol_string_ptr, *next_string_ptr, *next_symbol_string_ptr, *out_char_ptr, *start_char_ptr, *extra_out_char_ptr;
unsigned int i1, i2, num_symbols_defined, symbol, symbol_number, out_symbol_count;
unsigned int out_chars, chars_to_write, symbol_index, symbol_to_move, min_extra_reduce_index;
unsigned int mtf_queue[16][64];
unsigned int mtfg_queue_0[8], mtfg_queue_0_offset;
unsigned int mtfg_queue_8[8], mtfg_queue_8_offset;
unsigned int mtfg_queue_16[0x10], mtfg_queue_16_offset;
unsigned int mtfg_queue_32[0x20], mtfg_queue_32_offset;
unsigned int mtfg_queue_64[0x40], mtfg_queue_64_offset;
unsigned int mtfg_queue_128[0x40], mtfg_queue_128_offset;
unsigned int mtfg_queue_192[0x40], mtfg_queue_192_offset;
unsigned int big_sym_list[0x100];
unsigned int nsob[0x100][26];
unsigned int *mtf_queue_ptr, *mtf_queue_top_ptr;
unsigned int *symbol_array_start_ptr, *symbol_array_end_ptr, *symbol_array_ptr;
unsigned int *sym_list_ptrs[0x100][26];
unsigned short int nbob[0x100][26], sum_nbob[0x100], fbob[0x100][26];
volatile unsigned char output_ready, done_parsing;
volatile unsigned int out_symbol_array[0x40000];
FILE *fd_in, *fd_out;

struct sym_data {
  unsigned char type;  // bit 0: string ends CAP_CHAR, bit1: string starts a-z, bit2: nonergodic, bit3: in queue
      // bit 4: "word", bit 5: non-"word", bit 6: likely to be followed by ' ', bit 7: not likely to be followed by ' '
  unsigned char instances;
  unsigned char remaining;
  unsigned char starts;
  unsigned char ends;
  unsigned int string_index;
  unsigned int array_index;
} symbol_data[0x00C00000];


#include "GLZAmodel.h"



#define remove_mtfg_queue_symbol_16() { \
  while (mtfg_queue_position != 31) { \
    *(mtfg_queue_16 + ((mtfg_queue_16_offset + mtfg_queue_position) & 0xF)) \
        = *(mtfg_queue_16 + ((mtfg_queue_16_offset + mtfg_queue_position + 1) & 0xF)); \
    mtfg_queue_position++; \
  } \
  *(mtfg_queue_16 + ((mtfg_queue_16_offset - 1) & 0xF)) = *(mtfg_queue_32 + mtfg_queue_32_offset); \
  *(mtfg_queue_32 + mtfg_queue_32_offset) = *(mtfg_queue_64 + mtfg_queue_64_offset); \
  mtfg_queue_32_offset = (mtfg_queue_32_offset + 1) & 0x1F; \
  *(mtfg_queue_64 + mtfg_queue_64_offset) = *(mtfg_queue_128 + mtfg_queue_128_offset); \
  mtfg_queue_64_offset = (mtfg_queue_64_offset + 1) & 0x3F; \
  *(mtfg_queue_128 + mtfg_queue_128_offset) = *(mtfg_queue_192 + mtfg_queue_192_offset); \
  mtfg_queue_128_offset = (mtfg_queue_128_offset + 1) & 0x3F; \
  *(mtfg_queue_192 + mtfg_queue_192_offset) = MAX_SYMBOLS_DEFINED - 1; \
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F; \
}


#define remove_mtfg_queue_symbol_32() { \
  while (mtfg_queue_position != 63) { \
    *(mtfg_queue_32 + ((mtfg_queue_32_offset + mtfg_queue_position) & 0x1F)) \
        = *(mtfg_queue_32 + ((mtfg_queue_32_offset + mtfg_queue_position + 1) & 0x1F)); \
    mtfg_queue_position++; \
  } \
  *(mtfg_queue_32 + ((mtfg_queue_32_offset - 1) & 0x1F)) = *(mtfg_queue_64 + mtfg_queue_64_offset); \
  *(mtfg_queue_64 + mtfg_queue_64_offset) = *(mtfg_queue_128 + mtfg_queue_128_offset); \
  mtfg_queue_64_offset = (mtfg_queue_64_offset + 1) & 0x3F; \
  *(mtfg_queue_128 + mtfg_queue_128_offset) = *(mtfg_queue_192 + mtfg_queue_192_offset); \
  mtfg_queue_128_offset = (mtfg_queue_128_offset + 1) & 0x3F; \
  *(mtfg_queue_192 + mtfg_queue_192_offset) = MAX_SYMBOLS_DEFINED - 1; \
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F; \
}


#define remove_mtfg_queue_symbol_64() { \
  while (mtfg_queue_position != 127) { \
    *(mtfg_queue_64 + ((mtfg_queue_64_offset + mtfg_queue_position) & 0x3F)) \
        = *(mtfg_queue_64 + ((mtfg_queue_64_offset + mtfg_queue_position + 1) & 0x3F)); \
    mtfg_queue_position++; \
  } \
  *(mtfg_queue_64 + ((mtfg_queue_64_offset - 1) & 0x3F)) = *(mtfg_queue_128 + mtfg_queue_128_offset); \
  *(mtfg_queue_128 + mtfg_queue_128_offset) = *(mtfg_queue_192 + mtfg_queue_192_offset); \
  mtfg_queue_128_offset = (mtfg_queue_128_offset + 1) & 0x3F; \
  *(mtfg_queue_192 + mtfg_queue_192_offset) = MAX_SYMBOLS_DEFINED - 1; \
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F; \
}


#define remove_mtfg_queue_symbol_128() { \
  while (mtfg_queue_position != 191) { \
    *(mtfg_queue_128 + ((mtfg_queue_128_offset + mtfg_queue_position) & 0x3F)) \
        = *(mtfg_queue_128 + ((mtfg_queue_128_offset + mtfg_queue_position + 1) & 0x3F)); \
    mtfg_queue_position++; \
  } \
  *(mtfg_queue_128 + ((mtfg_queue_128_offset - 1) & 0x3F)) = *(mtfg_queue_192 + mtfg_queue_192_offset); \
  *(mtfg_queue_192 + mtfg_queue_192_offset) = MAX_SYMBOLS_DEFINED - 1; \
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F; \
}


#define remove_mtfg_queue_symbol_192() { \
  while (mtfg_queue_position != 255) { \
    *(mtfg_queue_192 + ((mtfg_queue_192_offset + mtfg_queue_position) & 0x3F)) \
        = *(mtfg_queue_192 + ((mtfg_queue_192_offset + mtfg_queue_position + 1) & 0x3F)); \
    mtfg_queue_position++; \
  } \
  *(mtfg_queue_192 + ((mtfg_queue_192_offset + 255) & 0x3F)) = MAX_SYMBOLS_DEFINED - 1; \
}


#define increment_mtfg_queue_0_8() { \
  mtfg_queue_0_offset = (mtfg_queue_0_offset - 1) & 7; \
  mtfg_queue_8_offset = (mtfg_queue_8_offset - 1) & 7; \
  mtfg_queue_symbol_15 = *(mtfg_queue_8 + mtfg_queue_8_offset); \
  *(mtfg_queue_8 + mtfg_queue_8_offset) = *(mtfg_queue_0 + mtfg_queue_0_offset); \
}


#define increment_mtfg_queue_16() { \
  mtfg_queue_16_offset = (mtfg_queue_16_offset - 1) & 0xF; \
  mtfg_queue_symbol_31 = *(mtfg_queue_16 + mtfg_queue_16_offset); \
  *(mtfg_queue_16 + mtfg_queue_16_offset) = mtfg_queue_symbol_15; \
}


#define increment_mtfg_queue_32() { \
  mtfg_queue_32_offset = (mtfg_queue_32_offset - 1) & 0x1F; \
  mtfg_queue_symbol_63 = *(mtfg_queue_32 + mtfg_queue_32_offset); \
  *(mtfg_queue_32 + mtfg_queue_32_offset) = mtfg_queue_symbol_31; \
}


#define increment_mtfg_queue_64() { \
  mtfg_queue_64_offset = (mtfg_queue_64_offset - 1) & 0x3F; \
  mtfg_queue_symbol_127 = *(mtfg_queue_64 + mtfg_queue_64_offset); \
  *(mtfg_queue_64 + mtfg_queue_64_offset) = mtfg_queue_symbol_63; \
}


#define increment_mtfg_queue_128() { \
  mtfg_queue_128_offset = (mtfg_queue_128_offset - 1) & 0x3F; \
  mtfg_queue_symbol_191 = *(mtfg_queue_128 + mtfg_queue_128_offset); \
  *(mtfg_queue_128 + mtfg_queue_128_offset) = mtfg_queue_symbol_127; \
}


#define increment_mtfg_queue_192() { \
  mtfg_queue_192_offset = (mtfg_queue_192_offset - 1) & 0x3F; \
  *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191; \
}


#define add_new_symbol_to_mtfg_queue(symbol_number) { \
  symbol_data[symbol_number].type |= 8; \
  mtfg_queue_8_offset = (mtfg_queue_8_offset - 1) & 7; \
  unsigned int mtfg_queue_symbol_15 = *(mtfg_queue_8 + mtfg_queue_8_offset); \
  mtfg_queue_0_offset = (mtfg_queue_0_offset - 1) & 7; \
  *(mtfg_queue_8 + mtfg_queue_8_offset) = *(mtfg_queue_0 + mtfg_queue_0_offset); \
  *(mtfg_queue_0 + mtfg_queue_0_offset) = symbol_number; \
  if (symbol_data[mtfg_queue_symbol_15].instances - MAX_INSTANCES_FOR_MTF_QUEUE > 12) { \
    mtfg_queue_16_offset = (mtfg_queue_16_offset - 1) & 0xF; \
    unsigned int mtfg_queue_symbol_31 = *(mtfg_queue_16 + mtfg_queue_16_offset); \
    *(mtfg_queue_16 + mtfg_queue_16_offset) = mtfg_queue_symbol_15; \
    if (symbol_data[mtfg_queue_symbol_31].instances - MAX_INSTANCES_FOR_MTF_QUEUE != 13) { \
      mtfg_queue_32_offset = (mtfg_queue_32_offset - 1) & 0x1F; \
      unsigned int mtfg_queue_symbol_63 = *(mtfg_queue_32 + mtfg_queue_32_offset); \
      *(mtfg_queue_32 + mtfg_queue_32_offset) = mtfg_queue_symbol_31; \
      if (symbol_data[mtfg_queue_symbol_63].instances - MAX_INSTANCES_FOR_MTF_QUEUE != 14) { \
        mtfg_queue_64_offset = (mtfg_queue_64_offset - 1) & 0x3F; \
        unsigned int mtfg_queue_symbol_127 = *(mtfg_queue_64 + mtfg_queue_64_offset); \
        *(mtfg_queue_64 + mtfg_queue_64_offset) = mtfg_queue_symbol_63; \
        if (symbol_data[mtfg_queue_symbol_127].instances - MAX_INSTANCES_FOR_MTF_QUEUE != 15) { \
          mtfg_queue_128_offset = (mtfg_queue_128_offset - 1) & 0x3F; \
          unsigned int mtfg_queue_symbol_191 = *(mtfg_queue_128 + mtfg_queue_128_offset); \
          *(mtfg_queue_128 + mtfg_queue_128_offset) = mtfg_queue_symbol_127; \
          if (symbol_data[mtfg_queue_symbol_191].instances - MAX_INSTANCES_FOR_MTF_QUEUE != 16) { \
            mtfg_queue_192_offset = (mtfg_queue_192_offset - 1) & 0x3F; \
            symbol_data[*(mtfg_queue_192 + mtfg_queue_192_offset)].type &= 0xF7; \
            *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191; \
          } \
          else \
            symbol_data[mtfg_queue_symbol_191].type &= 0xF7; \
        } \
        else \
          symbol_data[mtfg_queue_symbol_127].type &= 0xF7; \
      } \
      else \
        symbol_data[mtfg_queue_symbol_63].type &= 0xF7; \
    } \
    else \
      symbol_data[mtfg_queue_symbol_31].type &= 0xF7; \
  } \
  else \
    symbol_data[mtfg_queue_symbol_15].type &= 0xF7; \
}


#define update_mtfg_queue() { \
  unsigned int mtfg_queue_symbol_15, mtfg_queue_symbol_31, mtfg_queue_symbol_63, mtfg_queue_symbol_127, mtfg_queue_symbol_191; \
  if (mtfg_queue_position < 8) { \
    if (mtfg_queue_position < 5) { \
      symbol_number = mtfg_queue_0[(mtfg_queue_position += mtfg_queue_0_offset) & 7]; \
      while (mtfg_queue_position != mtfg_queue_0_offset) { \
        *(mtfg_queue_0 + (mtfg_queue_position & 7)) = *(mtfg_queue_0 + ((mtfg_queue_position - 1) & 7)); \
        mtfg_queue_position--; \
      } \
    } \
    else { \
      symbol_number = mtfg_queue_0[(mtfg_queue_position += mtfg_queue_0_offset) & 7]; \
      mtfg_queue_0_offset += 7; \
      while (mtfg_queue_position != mtfg_queue_0_offset) { \
        *(mtfg_queue_0 + (mtfg_queue_position & 7)) = *(mtfg_queue_0 + ((mtfg_queue_position + 1) & 7)); \
        mtfg_queue_position++; \
      } \
      mtfg_queue_0_offset = mtfg_queue_0_offset & 7; \
    } \
  } \
  else if (mtfg_queue_position < 32) { \
    if (mtfg_queue_position < 16) { \
      symbol_number = *(mtfg_queue_8 + ((mtfg_queue_position += mtfg_queue_8_offset - 8) & 7)); \
      while (mtfg_queue_position != mtfg_queue_8_offset) { \
        *(mtfg_queue_8 + (mtfg_queue_position & 7)) = *(mtfg_queue_8 + ((mtfg_queue_position - 1) & 7)); \
        mtfg_queue_position--; \
      } \
      mtfg_queue_0_offset = (mtfg_queue_0_offset - 1) & 7; \
      *(mtfg_queue_8 + mtfg_queue_8_offset) = *(mtfg_queue_0 + mtfg_queue_0_offset); \
    } \
    else { \
      symbol_number = *(mtfg_queue_16 + ((mtfg_queue_position + mtfg_queue_16_offset) & 0xF)); \
      increment_mtfg_queue_0_8(); \
      if (symbol_data[mtfg_queue_symbol_15].instances - MAX_INSTANCES_FOR_MTF_QUEUE <= 12) { \
        symbol_data[mtfg_queue_symbol_15].type &= 0xF7; \
        remove_mtfg_queue_symbol_16(); \
      } \
      else { \
        mtfg_queue_position += mtfg_queue_16_offset - 16; \
        while (mtfg_queue_position != mtfg_queue_16_offset) { \
          *(mtfg_queue_16 + (mtfg_queue_position & 0xF)) = *(mtfg_queue_16 + ((mtfg_queue_position - 1) & 0xF)); \
          mtfg_queue_position--; \
        } \
        *(mtfg_queue_16 + mtfg_queue_16_offset) = mtfg_queue_symbol_15; \
      } \
    } \
  } \
  else if (mtfg_queue_position < 64) { \
    symbol_number = *(mtfg_queue_32 + ((mtfg_queue_position + mtfg_queue_32_offset) & 0x1F)); \
    increment_mtfg_queue_0_8(); \
    if (symbol_data[mtfg_queue_symbol_15].instances - MAX_INSTANCES_FOR_MTF_QUEUE <= 12) { \
      symbol_data[mtfg_queue_symbol_15].type &= 0xF7; \
      remove_mtfg_queue_symbol_32(); \
    } \
    else { \
      increment_mtfg_queue_16(); \
      if (symbol_data[mtfg_queue_symbol_31].instances - MAX_INSTANCES_FOR_MTF_QUEUE == 13) { \
        symbol_data[mtfg_queue_symbol_31].type &= 0xF7; \
        remove_mtfg_queue_symbol_32(); \
      } \
      else { \
        mtfg_queue_position += mtfg_queue_32_offset - 32; \
        while (mtfg_queue_position != mtfg_queue_32_offset) { \
          *(mtfg_queue_32 + (mtfg_queue_position & 0x1F)) = *(mtfg_queue_32 + ((mtfg_queue_position - 1) & 0x1F)); \
          mtfg_queue_position--; \
        } \
        *(mtfg_queue_32 + mtfg_queue_32_offset) = mtfg_queue_symbol_31; \
      } \
    } \
  } \
  else if (mtfg_queue_position < 128) { \
    symbol_number = *(mtfg_queue_64 + ((mtfg_queue_position + mtfg_queue_64_offset) & 0x3F)); \
    increment_mtfg_queue_0_8(); \
    if (symbol_data[mtfg_queue_symbol_15].instances - MAX_INSTANCES_FOR_MTF_QUEUE <= 12) { \
      symbol_data[mtfg_queue_symbol_15].type &= 0xF7; \
      remove_mtfg_queue_symbol_64(); \
    } \
    else { \
      increment_mtfg_queue_16(); \
      if (symbol_data[mtfg_queue_symbol_31].instances - MAX_INSTANCES_FOR_MTF_QUEUE == 13) { \
        symbol_data[mtfg_queue_symbol_31].type &= 0xF7; \
        remove_mtfg_queue_symbol_64(); \
      } \
      else { \
        increment_mtfg_queue_32(); \
        if (symbol_data[mtfg_queue_symbol_63].instances - MAX_INSTANCES_FOR_MTF_QUEUE == 14) { \
          symbol_data[mtfg_queue_symbol_63].type &= 0xF7; \
          remove_mtfg_queue_symbol_64(); \
        } \
        else { \
          mtfg_queue_position += mtfg_queue_64_offset - 64; \
          while (mtfg_queue_position != mtfg_queue_64_offset) { \
            *(mtfg_queue_64 + (mtfg_queue_position & 0x3F)) = *(mtfg_queue_64 + ((mtfg_queue_position - 1) & 0x3F)); \
            mtfg_queue_position--; \
          } \
          *(mtfg_queue_64 + mtfg_queue_64_offset) = mtfg_queue_symbol_63; \
        } \
      } \
    } \
  } \
  else if (mtfg_queue_position < 192) { \
    symbol_number = *(mtfg_queue_128 + ((mtfg_queue_position + mtfg_queue_128_offset) & 0x3F)); \
    increment_mtfg_queue_0_8(); \
    if (symbol_data[mtfg_queue_symbol_15].instances - MAX_INSTANCES_FOR_MTF_QUEUE <= 12) { \
      symbol_data[mtfg_queue_symbol_15].type &= 0xF7; \
      remove_mtfg_queue_symbol_128(); \
    } \
    else { \
      increment_mtfg_queue_16(); \
      if (symbol_data[mtfg_queue_symbol_31].instances - MAX_INSTANCES_FOR_MTF_QUEUE == 13) { \
        symbol_data[mtfg_queue_symbol_31].type &= 0xF7; \
        remove_mtfg_queue_symbol_128(); \
      } \
      else { \
        increment_mtfg_queue_32(); \
        if (symbol_data[mtfg_queue_symbol_63].instances - MAX_INSTANCES_FOR_MTF_QUEUE == 14) { \
          symbol_data[mtfg_queue_symbol_63].type &= 0xF7; \
          remove_mtfg_queue_symbol_128(); \
        } \
        else { \
          increment_mtfg_queue_64(); \
          if (symbol_data[mtfg_queue_symbol_127].instances - MAX_INSTANCES_FOR_MTF_QUEUE == 15) { \
            symbol_data[mtfg_queue_symbol_127].type &= 0xF7; \
            remove_mtfg_queue_symbol_128(); \
          } \
          else { \
            mtfg_queue_position += mtfg_queue_128_offset - 128; \
            while (mtfg_queue_position != mtfg_queue_128_offset) { \
              *(mtfg_queue_128 + (mtfg_queue_position & 0x3F)) = *(mtfg_queue_128 + ((mtfg_queue_position - 1) & 0x3F)); \
              mtfg_queue_position--; \
            } \
            *(mtfg_queue_128 + mtfg_queue_128_offset) = mtfg_queue_symbol_127; \
          } \
        } \
      } \
    } \
  } \
  else { \
    symbol_number = *(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F)); \
    increment_mtfg_queue_0_8(); \
    if (symbol_data[mtfg_queue_symbol_15].instances - MAX_INSTANCES_FOR_MTF_QUEUE <= 12) { \
      symbol_data[mtfg_queue_symbol_15].type &= 0xF7; \
      remove_mtfg_queue_symbol_192(); \
    } \
    else { \
      increment_mtfg_queue_16(); \
      if (symbol_data[mtfg_queue_symbol_31].instances - MAX_INSTANCES_FOR_MTF_QUEUE == 13) { \
        symbol_data[mtfg_queue_symbol_31].type &= 0xF7; \
        remove_mtfg_queue_symbol_192(); \
      } \
      else { \
        increment_mtfg_queue_32(); \
        if (symbol_data[mtfg_queue_symbol_63].instances - MAX_INSTANCES_FOR_MTF_QUEUE == 14) { \
          symbol_data[mtfg_queue_symbol_63].type &= 0xF7; \
          remove_mtfg_queue_symbol_192(); \
        } \
        else { \
          increment_mtfg_queue_64(); \
          if (symbol_data[mtfg_queue_symbol_127].instances - MAX_INSTANCES_FOR_MTF_QUEUE == 15) { \
            symbol_data[mtfg_queue_symbol_127].type &= 0xF7; \
            remove_mtfg_queue_symbol_192(); \
          } \
          else { \
            increment_mtfg_queue_128(); \
            if (symbol_data[mtfg_queue_symbol_191].instances - MAX_INSTANCES_FOR_MTF_QUEUE == 16) { \
              symbol_data[mtfg_queue_symbol_191].type &= 0xF7; \
              remove_mtfg_queue_symbol_192(); \
            } \
            else { \
              mtfg_queue_position += mtfg_queue_192_offset - 192; \
              while (mtfg_queue_position != mtfg_queue_192_offset) { \
                *(mtfg_queue_192 + (mtfg_queue_position & 0x3F)) = *(mtfg_queue_192 + ((mtfg_queue_position - 1) & 0x3F)); \
                mtfg_queue_position--; \
              } \
              *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191; \
            } \
          } \
        } \
      } \
    } \
  } \
  *(mtfg_queue_0 + mtfg_queue_0_offset) = symbol_number; \
}


#define get_mtfg_symbol() { \
  DecodeMtfgQueuePosStart(NOT_CAP); \
  if (DecodeMtfgQueuePosCheck0(NOT_CAP)) { \
    DecodeMtfgQueuePosFinish0(NOT_CAP); \
    symbol_number = mtfg_queue_0[mtfg_queue_0_offset & 7]; \
  } \
  else { \
    DecodeMtfgQueuePosFinish(NOT_CAP); \
    update_mtfg_queue(); \
  } \
}



#define get_mtfg_symbol_cap() { \
  DecodeMtfgQueuePosStart(CAP); \
  if (DecodeMtfgQueuePosCheck0(CAP)) { \
    DecodeMtfgQueuePosFinish0(CAP); \
    unsigned int find_caps = 1; \
    unsigned int cap_queue_position = mtfg_queue_0_offset; \
    do { \
      if (symbol_data[*(mtfg_queue_0 + cap_queue_position)].type & 2) { \
        find_caps = 0; \
        break; \
      } \
      else \
        mtfg_queue_position++; \
      cap_queue_position = (cap_queue_position + 1) & 7; \
    } while (cap_queue_position != mtfg_queue_0_offset); \
    if (find_caps) { \
      cap_queue_position = mtfg_queue_8_offset; \
      do { \
        if (symbol_data[*(mtfg_queue_8 + cap_queue_position)].type & 2) { \
          find_caps = 0; \
          break; \
        } \
        else \
          mtfg_queue_position++; \
        cap_queue_position = (cap_queue_position + 1) & 7; \
      } while (cap_queue_position != mtfg_queue_8_offset); \
      if (find_caps) { \
        cap_queue_position = mtfg_queue_16_offset; \
        do { \
          if (symbol_data[*(mtfg_queue_16 + cap_queue_position)].type & 2) { \
            find_caps = 0; \
            break; \
          } \
          else \
            mtfg_queue_position++; \
          cap_queue_position = (cap_queue_position + 1) & 0xF; \
        } while (cap_queue_position != mtfg_queue_16_offset); \
        if (find_caps) { \
          cap_queue_position = mtfg_queue_32_offset; \
          do { \
            if (symbol_data[*(mtfg_queue_32 + cap_queue_position)].type & 2) { \
              find_caps = 0; \
              break; \
            } \
            else \
              mtfg_queue_position++; \
            cap_queue_position = (cap_queue_position + 1) & 0x1F; \
          } while (cap_queue_position != mtfg_queue_32_offset); \
          if (find_caps) { \
            cap_queue_position = mtfg_queue_64_offset; \
            do { \
              if (symbol_data[*(mtfg_queue_64 + cap_queue_position)].type & 2) { \
                find_caps = 0; \
                break; \
              } \
              else \
                mtfg_queue_position++; \
              cap_queue_position = (cap_queue_position + 1) & 0x3F; \
            } while (cap_queue_position != mtfg_queue_64_offset); \
            if (find_caps) { \
              cap_queue_position = mtfg_queue_128_offset; \
              do { \
                if (symbol_data[*(mtfg_queue_128 + cap_queue_position)].type & 2) { \
                  find_caps = 0; \
                  break; \
                } \
                else \
                  mtfg_queue_position++; \
                cap_queue_position = (cap_queue_position + 1) & 0x3F; \
              } while (cap_queue_position != mtfg_queue_128_offset); \
              if (find_caps) { \
                cap_queue_position = mtfg_queue_192_offset; \
                while (symbol_data[*(mtfg_queue_192 + cap_queue_position)].type & 2) { \
                  mtfg_queue_position++; \
                  cap_queue_position = (cap_queue_position + 1) & 0x3F; \
                } while (1); \
              } \
            } \
          } \
        } \
      } \
    } \
  } \
  else { \
    DecodeMtfgQueuePosFinish(CAP); \
    unsigned int find_caps = mtfg_queue_position + 1; \
    unsigned int cap_queue_position = mtfg_queue_0_offset; \
    do { \
      if (symbol_data[*(mtfg_queue_0 + cap_queue_position)].type & 2) { \
        find_caps--; \
        if (find_caps == 0) \
          break; \
      } \
      else \
        mtfg_queue_position++; \
      cap_queue_position = (cap_queue_position + 1) & 7; \
    } while (cap_queue_position != mtfg_queue_0_offset); \
    if (find_caps) { \
      cap_queue_position = mtfg_queue_8_offset; \
      do { \
        if (symbol_data[*(mtfg_queue_8 + cap_queue_position)].type & 2) { \
          find_caps--; \
          if (find_caps == 0) \
            break; \
        } \
        else \
          mtfg_queue_position++; \
        cap_queue_position = (cap_queue_position + 1) & 7; \
      } while (cap_queue_position != mtfg_queue_8_offset); \
      if (find_caps) { \
        cap_queue_position = mtfg_queue_16_offset; \
        do { \
          if (symbol_data[*(mtfg_queue_16 + cap_queue_position)].type & 2) { \
            find_caps--; \
            if (find_caps == 0) \
              break; \
          } \
          else \
            mtfg_queue_position++; \
          cap_queue_position = (cap_queue_position + 1) & 0xF; \
        } while (cap_queue_position != mtfg_queue_16_offset); \
        if (find_caps) { \
          cap_queue_position = mtfg_queue_32_offset; \
          do { \
            if (symbol_data[*(mtfg_queue_32 + cap_queue_position)].type & 2) { \
              find_caps--; \
              if (find_caps == 0) \
                break; \
            } \
            else \
              mtfg_queue_position++; \
            cap_queue_position = (cap_queue_position + 1) & 0x1F; \
          } while (cap_queue_position != mtfg_queue_32_offset); \
          if (find_caps) { \
            cap_queue_position = mtfg_queue_64_offset; \
            do { \
              if (symbol_data[*(mtfg_queue_64 + cap_queue_position)].type & 2) { \
                find_caps--; \
                if (find_caps == 0) \
                  break; \
              } \
              else \
                mtfg_queue_position++; \
              cap_queue_position = (cap_queue_position + 1) & 0x3F; \
            } while (cap_queue_position != mtfg_queue_64_offset); \
            if (find_caps) { \
              cap_queue_position = mtfg_queue_128_offset; \
              do { \
                if (symbol_data[*(mtfg_queue_128 + cap_queue_position)].type & 2) { \
                  find_caps--; \
                  if (find_caps == 0) \
                    break; \
                } \
                else \
                  mtfg_queue_position++; \
                cap_queue_position = (cap_queue_position + 1) & 0x3F; \
              } while (cap_queue_position != mtfg_queue_128_offset); \
              if (find_caps) { \
                cap_queue_position = mtfg_queue_192_offset; \
                do { \
                  if (symbol_data[*(mtfg_queue_192 + cap_queue_position)].type & 2) { \
                    if (--find_caps == 0) \
                      break; \
                  } \
                  else \
                    mtfg_queue_position++; \
                  cap_queue_position = (cap_queue_position + 1) & 0x3F; \
                } while (1); \
              } \
            } \
          } \
        } \
      } \
    } \
  } \
  update_mtfg_queue(); \
}


#define add_dictionary_symbol(symbol, bits) { \
  unsigned char first_char = symbol_data[symbol].starts; \
  if ((nsob[first_char][bits] == INITIAL_LIST_SIZE) && ((big_sym_list[first_char] & (1 << bits)) == 0)) { \
    big_sym_list[first_char] |= 1 << bits; \
    sym_list_ptrs[first_char][bits] \
        = (unsigned int *)realloc(sym_list_ptrs[first_char][bits], sizeof(unsigned int) * BIG_LIST_SIZE); \
  } \
  symbol_data[symbol].array_index = nsob[first_char][bits]; \
  sym_list_ptrs[first_char][bits][nsob[first_char][bits]++] = symbol; \
  if ((nsob[first_char][bits] << (32 - bits)) \
      > ((unsigned int)nbob[first_char][bits] << (32 - bin_bits_under_max[first_char]))) { \
    if (bits >= bin_bits_under_max[first_char]) { /* add a bin */ \
      if (++sum_nbob[first_char] <= 0x1000) { \
        if (bits == max_code_length) \
          nbob[first_char][bits]++; \
        else { \
          lookup_bits[first_char][fbob[first_char][bits] + nbob[first_char][bits]++] = bits; \
          unsigned char temp_bits = bits; \
          while (++temp_bits != max_code_length) { \
            if (nbob[first_char][temp_bits]) \
              lookup_bits[first_char][fbob[first_char][temp_bits] + nbob[first_char][temp_bits]] = temp_bits; \
            fbob[first_char][temp_bits]++; \
          } \
          fbob[first_char][max_code_length]++; \
        } \
      } \
      else { \
        nbob[first_char][bits]++; \
        unsigned char code_length; \
        do { \
          bin_bits_under_max[first_char]--; \
          sum_nbob[first_char] = 0; \
          for (code_length = 1 ; code_length <= max_code_length ; code_length++) \
            sum_nbob[first_char] += (nbob[first_char][code_length] = (nbob[first_char][code_length] + 1) >> 1); \
        } while (sum_nbob[first_char] > 0x1000); \
        unsigned short int bin = nbob[first_char][1]; \
        unsigned char temp_bits; \
        for (temp_bits = 1 ; temp_bits <= max_code_length ; temp_bits++) { \
          fbob[first_char][temp_bits] = bin; \
          bin += nbob[first_char][temp_bits]; \
        } \
        bin = 0; \
        for (code_length = 1 ; code_length < max_code_length ; code_length++) \
          while (bin < fbob[first_char][code_length+1]) \
            lookup_bits[first_char][bin++] = code_length; \
        while (bin < 0x1000) \
          lookup_bits[first_char][bin++] = max_code_length; \
      } \
    } \
    else { /* add multiple bins */ \
      unsigned int new_bins = 1 << (bin_bits_under_max[first_char] - bits); \
      if (sum_nbob[first_char] + new_bins <= 0x1000) { \
        sum_nbob[first_char] += new_bins; \
        do { \
          lookup_bits[first_char][fbob[first_char][bits] + nbob[first_char][bits]] = bits; \
          nbob[first_char][bits]++; \
          unsigned char temp_bits = bits; \
          while (++temp_bits != max_code_length) { \
            if (nbob[first_char][temp_bits]) \
              lookup_bits[first_char][fbob[first_char][temp_bits] + nbob[first_char][temp_bits]] = temp_bits; \
            fbob[first_char][temp_bits]++; \
          } \
        } while ((nsob[first_char][bits] << (bin_bits_under_max[first_char] - bits)) > (unsigned int)nbob[first_char][bits]); \
        fbob[first_char][max_code_length] += 1 << (bin_bits_under_max[first_char] - bits); \
      } \
      else if (new_bins <= 0x1000) { \
        unsigned char bin_shift; \
        nbob[first_char][bits] += new_bins; \
        unsigned char code_length; \
        do { \
          bin_bits_under_max[first_char]--; \
          sum_nbob[first_char] = 0; \
          for (code_length = 1 ; code_length <= max_code_length ; code_length++) \
            sum_nbob[first_char] += (nbob[first_char][code_length] = (nbob[first_char][code_length] + 1) >> 1); \
        } while (sum_nbob[first_char] > 0x1000); \
        unsigned short int bin = nbob[first_char][1]; \
        unsigned char temp_bits; \
        for (temp_bits = 2 ; temp_bits <= max_code_length ; temp_bits++) { \
          fbob[first_char][temp_bits] = bin; \
          bin += nbob[first_char][temp_bits]; \
        } \
        bin = 0; \
        for (code_length = 1 ; code_length < max_code_length ; code_length++) \
          while (bin < fbob[first_char][code_length+1]) \
            lookup_bits[first_char][bin++] = code_length; \
        while (bin < 0x1000) \
          lookup_bits[first_char][bin++] = max_code_length; \
      } \
      else { \
        unsigned char bin_shift = bin_bits_under_max[first_char] - 12 - bits; \
        if (sum_nbob[first_char]) \
          bin_shift++; \
        bin_bits_under_max[first_char] -= bin_shift; \
        sum_nbob[first_char] = 0; \
        unsigned char code_length; \
        for (code_length = 1 ; code_length <= max_code_length ; code_length++) \
          sum_nbob[first_char] += (nbob[first_char][code_length] \
              = (nbob[first_char][code_length] + (1 << bin_shift) - 1) >> bin_shift); \
        nbob[first_char][bits] += new_bins >> bin_shift; \
        sum_nbob[first_char] += new_bins >> bin_shift; \
        unsigned short int bin = nbob[first_char][1]; \
        unsigned char temp_bits; \
        for (temp_bits = 1 ; temp_bits <= max_code_length ; temp_bits++) { \
          fbob[first_char][temp_bits] = bin; \
          bin += nbob[first_char][temp_bits]; \
        } \
        bin = 0; \
        for (code_length = 1 ; code_length < max_code_length ; code_length++) \
          while (bin < fbob[first_char][code_length+1]) \
            lookup_bits[first_char][bin++] = code_length; \
        while (bin < 0x1000) \
          lookup_bits[first_char][bin++] = max_code_length; \
      } \
    } \
  } \
}


#define remove_dictionary_symbol(symbol, bits) { \
  unsigned char first_char = symbol_data[symbol].starts; \
  sym_list_ptrs[first_char][bits][symbol_data[symbol].array_index] = sym_list_ptrs[first_char][bits][--nsob[first_char][bits]]; \
  symbol_data[sym_list_ptrs[first_char][bits][nsob[first_char][bits]]].array_index = symbol_data[symbol].array_index; \
}


#define insert_mtf_queue(cap_type) { \
  remove_dictionary_symbol(symbol_number,CodeLength); \
  if (--symbol_data[symbol_number].remaining) { \
    symbol_count = symbol_data[symbol_number].instances; \
    mtf_queue_number = symbol_count - 2; \
    UpFreqMtfQueueNumD(cap_type); \
    if (mtf_queue_size[symbol_count] != MTF_QUEUE_SIZE) \
      mtf_queue[symbol_count][((mtf_queue_offset[symbol_count] + mtf_queue_size[symbol_count]++) & 0x3F)] = symbol_number; \
    else { \
      mtf_queue_ptr = &mtf_queue[symbol_count][mtf_queue_offset[symbol_count]++ & 0x3F]; \
      add_dictionary_symbol(*mtf_queue_ptr,CodeLength); \
      *mtf_queue_ptr = symbol_number; \
    } \
  } \
}


#define get_long_symbol() { \
  char index_bits = CodeLength - bin_bits_under_max[FirstChar]; \
  unsigned int msib = nbob[FirstChar][CodeLength] << index_bits; \
  unsigned int shifted_max_symbols = msib >> 1; \
  unsigned int * sym_list_ptr = sym_list_ptrs[FirstChar][CodeLength]; \
  if (shifted_max_symbols >= nsob[FirstChar][CodeLength]) { \
    unsigned int reduce_bits = 1; \
    while ((shifted_max_symbols >>= 1) >= nsob[FirstChar][CodeLength]) \
      reduce_bits++; \
    if (index_bits <= reduce_bits) { \
      SymbolIndex = BinNum - fbob[FirstChar][CodeLength]; \
      unsigned int extra_code_bins = 0; \
      if (SymbolIndex) { \
        int index = SymbolIndex; \
        if (symbol_data[sym_list_ptr[--index]].type & 8) { \
          extra_code_bins++; \
          while (index && (symbol_data[sym_list_ptr[--index]].type & 8)) \
            extra_code_bins++; \
        } \
        low -= range * extra_code_bins; \
        while (symbol_data[sym_list_ptr[SymbolIndex]].type & 8) { \
          extra_code_bins++; \
          SymbolIndex++; \
        } \
        range *= 1 + extra_code_bins; \
        symbol_number = sym_list_ptr[SymbolIndex]; \
      } \
      else if ((FirstChar == end_symbol) && (CodeLength == max_code_length)) \
        break; /* EOF */ \
      else { \
        if (symbol_data[sym_list_ptr[SymbolIndex]].type & 8) { \
          while (symbol_data[sym_list_ptr[++SymbolIndex]].type & 8) \
            extra_code_bins++; \
          range *= 2 + extra_code_bins; \
        } \
        symbol_number = sym_list_ptr[SymbolIndex]; \
      } \
    } \
    else { \
      index_bits -= reduce_bits; \
      min_extra_reduce_index = (nsob[FirstChar][CodeLength] << 1) - (msib >> reduce_bits); \
      DecodeDictionarySymbolIndex(index_bits,fbob[FirstChar][CodeLength],sym_list_ptr); \
    } \
  } \
  else { \
    min_extra_reduce_index = (nsob[FirstChar][CodeLength] << 1) - msib; \
    DecodeDictionarySymbolIndex(index_bits,fbob[FirstChar][CodeLength],sym_list_ptr); \
  } \
}


#define get_short_symbol() { \
  unsigned int extra_code_bins = 0; \
  unsigned int index = (BinNum - fbob[FirstChar][CodeLength]) >> (bin_bits_under_max[FirstChar] - CodeLength); \
  int temp_index = index; \
  if (temp_index && (symbol_data[sym_list_ptrs[FirstChar][CodeLength][--temp_index]].type & 8)) { \
    extra_code_bins++; \
    while (temp_index && (symbol_data[sym_list_ptrs[FirstChar][CodeLength][--temp_index]].type & 8)) \
      extra_code_bins++; \
    low -= range * extra_code_bins; \
    while (symbol_data[sym_list_ptrs[FirstChar][CodeLength][index]].type & 8) { \
      index++; \
      extra_code_bins++; \
    } \
    range *= 1 + extra_code_bins; \
  } \
  else if (symbol_data[sym_list_ptrs[FirstChar][CodeLength][index]].type & 8) { \
    extra_code_bins++; \
    while (symbol_data[sym_list_ptrs[FirstChar][CodeLength][++index]].type & 8) \
      extra_code_bins++; \
    range *= 1 + extra_code_bins; \
  } \
  symbol_number = sym_list_ptrs[FirstChar][CodeLength][index]; \
}


void get_mtf_symbol() {
  DecodeMtfQueueNumStart(NOT_CAP);
  if (DecodeMtfQueueNumCheck0(NOT_CAP)) {
    DecodeMtfQueueNumFinish0(NOT_CAP);
    DecodeMtfQueuePosStart(NOT_CAP, 0);
    if (DecodeMtfQueuePosCheck0(NOT_CAP, 0)) {
      DecodeMtfQueuePosFinish0(NOT_CAP, 0);
      symbol_number = mtf_queue[2][(mtf_queue_offset[2] + --mtf_queue_size[2]) & 0x3F];
    }
    else {
      DecodeMtfQueuePosFinish(NOT_CAP, 0);
      unsigned int mtf_queue_last_position = (mtf_queue_offset[2] + --mtf_queue_size[2]) & 0x3F;
      unsigned int mtf_queue_position = (mtf_queue_last_position - Symbol) & 0x3F;
      symbol_number = *((mtf_queue_ptr = &mtf_queue[2][0]) + mtf_queue_position);
      do { // move the newer symbols up
        *(mtf_queue_ptr + mtf_queue_position) = *(mtf_queue_ptr + ((mtf_queue_position + 1) & 0x3F));
      } while ((mtf_queue_position = (mtf_queue_position + 1) & 0x3F) != mtf_queue_last_position);
    }
  }
  else {
    DecodeMtfQueueNumFinish(NOT_CAP);
    DecodeMtfQueuePosStart(NOT_CAP, mtf_queue_number);
    if (DecodeMtfQueuePosCheck0(NOT_CAP, mtf_queue_number)) {
      DecodeMtfQueuePosFinish0(NOT_CAP, mtf_queue_number);
      mtf_queue_number += 2;
      symbol_number = mtf_queue[mtf_queue_number]
          [(mtf_queue_offset[mtf_queue_number] + mtf_queue_size[mtf_queue_number] - 1) & 0x3F];
      // decrement the mtf queue size if this is the last instance of this symbol
      if (--symbol_data[symbol_number].remaining) {
        mtf_queue_number -= 2;
        UpFreqMtfQueueNumHitD(NOT_CAP);
      }
      else
        mtf_queue_size[mtf_queue_number]--;
    }
    else {
      DecodeMtfQueuePosFinish(NOT_CAP, mtf_queue_number);
      mtf_queue_number += 2;
      unsigned int mtf_queue_last_position
          = (mtf_queue_offset[mtf_queue_number] + mtf_queue_size[mtf_queue_number] - 1) & 0x3F;
      unsigned int mtf_queue_position = (mtf_queue_last_position - Symbol) & 0x3F;
      // remove this symbol from its current mtf queue position
      symbol_number = *((mtf_queue_ptr = &mtf_queue[mtf_queue_number][0]) + mtf_queue_position);
      do { // move the newer symbols up
        *(mtf_queue_ptr + mtf_queue_position) = *(mtf_queue_ptr + ((mtf_queue_position + 1) & 0x3F));
        mtf_queue_position = (mtf_queue_position + 1) & 0x3F;
      } while (mtf_queue_position != mtf_queue_last_position);
      if (--symbol_data[symbol_number].remaining) { // put symbol on top of mtf queue
        *(mtf_queue_ptr + mtf_queue_position) = symbol_number;
        mtf_queue_number -= 2;
        UpFreqMtfQueueNumHitD(NOT_CAP);
      }
      else // last instance - decrement the mtf queue size
        mtf_queue_size[mtf_queue_number]--;
    }
  }
}


void get_mtf_symbol_cap() {
  DecodeMtfQueueNumStart(CAP);
  if (DecodeMtfQueueNumCheck0(CAP)) {
    DecodeMtfQueueNumFinish0(CAP);
    DecodeMtfQueuePosStart(CAP, 0);
    if (DecodeMtfQueuePosCheck0(CAP, 0)) {
      DecodeMtfQueuePosFinish0(CAP, 0);
      unsigned char num_az = 0;
      mtf_queue_ptr = mtf_queue_top_ptr = &mtf_queue[2][(mtf_queue_offset[2] + --mtf_queue_size[2]) & 0x3F];
      while ((symbol_data[*mtf_queue_ptr].type & 2) == 0) {
        if (mtf_queue_ptr-- == &mtf_queue[2][0])
          mtf_queue_ptr += MTF_QUEUE_SIZE;
      }
      symbol_number = *mtf_queue_ptr;
      while (mtf_queue_ptr != mtf_queue_top_ptr) { // move the higher symbols down
        if (mtf_queue_ptr < &mtf_queue[2][0] + MTF_QUEUE_SIZE - 1) {
          *mtf_queue_ptr = *(mtf_queue_ptr + 1);
          mtf_queue_ptr++;
        }
        else {
          *mtf_queue_ptr = *(mtf_queue_ptr - MTF_QUEUE_SIZE + 1);
          mtf_queue_ptr -= MTF_QUEUE_SIZE - 1;
        }
      }
    }
    else {
      DecodeMtfQueuePosFinish(CAP, 0);
      unsigned char num_az = Symbol + 1;
      mtf_queue_ptr = (mtf_queue_top_ptr = &mtf_queue[2][(mtf_queue_offset[2] + --mtf_queue_size[2]) & 0x3F]) + 1;
      // remove this symbol from its current mtf queue position
      do {
        if (mtf_queue_ptr != &mtf_queue[2][0])
          mtf_queue_ptr--;
        else
          mtf_queue_ptr += MTF_QUEUE_SIZE - 1;
        if (symbol_data[*mtf_queue_ptr].type & 2)
          num_az--;
      } while (num_az);
      symbol_number = *mtf_queue_ptr;
      do { // move the higher symbols down
        if (mtf_queue_ptr < &mtf_queue[2][0] + MTF_QUEUE_SIZE - 1) {
          *mtf_queue_ptr = *(mtf_queue_ptr + 1);
          mtf_queue_ptr++;
        }
        else {
          *mtf_queue_ptr = *(mtf_queue_ptr - MTF_QUEUE_SIZE + 1);
          mtf_queue_ptr -= MTF_QUEUE_SIZE - 1;
        }
      } while (mtf_queue_ptr != mtf_queue_top_ptr);
    }
  }
  else {
    DecodeMtfQueueNumFinish(CAP);
    DecodeMtfQueuePosStart(CAP, mtf_queue_number);
    if (DecodeMtfQueuePosCheck0(CAP, mtf_queue_number)) {
      DecodeMtfQueuePosFinish0(CAP, mtf_queue_number);
      mtf_queue_number += 2;
      unsigned char num_az = 0;
      mtf_queue_ptr = mtf_queue_top_ptr = &mtf_queue[mtf_queue_number]
          [(mtf_queue_offset[mtf_queue_number] + mtf_queue_size[mtf_queue_number] - 1) & 0x3F];
      while ((symbol_data[*mtf_queue_ptr].type & 2) == 0) {
        if (mtf_queue_ptr-- == &mtf_queue[mtf_queue_number][0])
          mtf_queue_ptr += MTF_QUEUE_SIZE;
      }
      symbol_number = *mtf_queue_ptr;
      while (mtf_queue_ptr != mtf_queue_top_ptr) { // move the higher symbols down
        if (mtf_queue_ptr < &mtf_queue[mtf_queue_number][0] + MTF_QUEUE_SIZE - 1) {
          *mtf_queue_ptr = *(mtf_queue_ptr + 1);
          mtf_queue_ptr++;
        }
        else {
          *mtf_queue_ptr = *(mtf_queue_ptr - MTF_QUEUE_SIZE + 1);
          mtf_queue_ptr -= MTF_QUEUE_SIZE - 1;
        }
      }
    }
    else {
      DecodeMtfQueuePosFinish(CAP, mtf_queue_number);
      mtf_queue_number += 2;
      mtf_queue_ptr = (mtf_queue_top_ptr = &mtf_queue[mtf_queue_number]
          [(mtf_queue_offset[mtf_queue_number] + mtf_queue_size[mtf_queue_number] - 1) & 0x3F]) + 1;
      // remove this symbol from its current mtf queue position
      unsigned char num_az = Symbol + 1;
      do {
        if (mtf_queue_ptr != &mtf_queue[mtf_queue_number][0])
          mtf_queue_ptr--;
        else
          mtf_queue_ptr += MTF_QUEUE_SIZE - 1;
        if (symbol_data[*mtf_queue_ptr].type & 2)
          num_az--;
      } while (num_az);

      symbol_number = *mtf_queue_ptr;
      do { // move the higher symbols down
        if (mtf_queue_ptr < &mtf_queue[mtf_queue_number][0] + MTF_QUEUE_SIZE - 1) {
          *mtf_queue_ptr = *(mtf_queue_ptr + 1);
          mtf_queue_ptr++;
        }
        else {
          *mtf_queue_ptr = *(mtf_queue_ptr - MTF_QUEUE_SIZE + 1);
          mtf_queue_ptr -= MTF_QUEUE_SIZE - 1;
        }
      } while (mtf_queue_ptr != mtf_queue_top_ptr);
    }
    if (--symbol_data[symbol_number].remaining) { // put symbol on top of mtf queue
      *mtf_queue_ptr = symbol_number;
      mtf_queue_number -= 2;
      UpFreqMtfQueueNumHitD(CAP);
    }
    else // last instance - decrement the mtf queue size
      mtf_queue_size[mtf_queue_number]--;
  }
}


#define get_extra_length() { \
  unsigned char temp_bits, data_bits = 0; \
  unsigned int SymsInDef; \
  DecodeExtraLength(); \
  while (Symbol == 3) { \
    data_bits += 2; \
    DecodeExtraLength(); \
  } \
  if (Symbol == 2) { \
    data_bits += 2; \
    temp_bits = data_bits; \
    SymsInDef = 0; \
  } \
  else { \
    temp_bits = data_bits++; \
    SymsInDef = Symbol; \
  } \
  while (temp_bits) { \
    temp_bits -= 2; \
    DecodeExtraLength(); \
    SymsInDef = (SymsInDef << 2) + Symbol; \
  } \
  symbols_in_definition = SymsInDef + (1 << data_bits) + 14; \
}


#define copy_string(in, end_in, out) { \
  while (end_in - in >= 8) { \
    *out = *in; \
    *(out + 1) = *(in + 1); \
    *(out + 2) = *(in + 2); \
    *(out + 3) = *(in + 3); \
    *(out + 4) = *(in + 4); \
    *(out + 5) = *(in + 5); \
    *(out + 6) = *(in + 6); \
    *(out + 7) = *(in + 7); \
    out += 8; \
    in += 8; \
  } \
  while (in != end_in) \
    *out++ = *in++; \
}


#define copy_string_delta(in, end_in, out) { \
  while ((delta_on == 0) && (in != end_in)) { \
    if (out >= out_char0 + 4 + delta_gap) { \
      delta_on = 1; \
      *out = *(out - delta_gap) + *in++; \
      out++; \
    } \
    else \
      *out++ = *in++; \
  } \
  while (in != end_in) { \
    *out = *(out - delta_gap) + *in++; \
    out++; \
  } \
}


unsigned char* decode_define(unsigned char* define_string) {
  unsigned char define_symbol_instances, define_symbol_code_length, *define_string_ptr, *end_define_string_ptr;
  unsigned int symbols_in_definition;

  end_define_string_ptr = define_string;

  DecodeSIDStart(NOT_CAP);
  if (DecodeSIDCheck0(NOT_CAP)) {
    DecodeSIDFinish0(NOT_CAP);
    DecodeINSTStart(NOT_CAP);
    if (DecodeINSTCheck0(NOT_CAP)) {
      DecodeINSTFinish0(NOT_CAP);
      define_symbol_instances = 2;
      define_symbol_code_length = max_code_length;
    }
    else {
      DecodeINSTFinish(NOT_CAP);
      if (Instances >= MAX_INSTANCES_FOR_MTF_QUEUE) {
        define_symbol_instances = 0;
        define_symbol_code_length = max_regular_code_length + MAX_INSTANCES_FOR_MTF_QUEUE - Instances;
      }
      else if (Instances != MAX_INSTANCES_FOR_MTF_QUEUE - 1) {
        define_symbol_instances = Instances + 2;
        define_symbol_code_length = mtf_queue_miss_code_length[define_symbol_instances];
      }
      else
        define_symbol_instances = 1;
    }

    DecodeBaseSymbol(base_bits);
    if (UTF8_compliant) {
      if (BaseSymbol < 0x80) {
        unsigned char j1 = 0x80;
        do {
          if (RangeScaleFirstChar[0][j1]) {
            unsigned char j2 = 0x80;
            while (SymbolFirstChar[0][j1][j2] != (unsigned char)BaseSymbol)
              j2--;
            FreqFirstChar[0][j1][j2] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[0][j1] += UP_FREQ_FIRST_CHAR;
            if (RangeScaleFirstChar[0][j1] > FREQ_FIRST_CHAR_BOT)
              rescaleFirstChar(0, j1);
          }
          if (RangeScaleFirstChar[1][j1]) {
            unsigned char j2 = 0x80;
            while (SymbolFirstChar[1][j1][j2] != (unsigned char)BaseSymbol)
              j2--;
            FreqFirstChar[1][j1][j2] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[1][j1] += UP_FREQ_FIRST_CHAR;
            if (RangeScaleFirstChar[1][j1] > FREQ_FIRST_CHAR_BOT)
              rescaleFirstChar(1, j1);
          }
          if (RangeScaleFirstChar[2][j1]) {
            unsigned char j2 = 0x80;
            while (SymbolFirstChar[2][j1][j2] != (unsigned char)BaseSymbol)
              j2--;
            FreqFirstChar[2][j1][j2] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[2][j1] += UP_FREQ_FIRST_CHAR;
            if (RangeScaleFirstChar[2][j1] > FREQ_FIRST_CHAR_BOT)
              rescaleFirstChar(2, j1);
          }
          if (RangeScaleFirstChar[3][j1]) {
            unsigned char j2 = 0x80;
            while (SymbolFirstChar[3][j1][j2] != (unsigned char)BaseSymbol)
              j2--;
            FreqFirstChar[3][j1][j2] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[3][j1] += UP_FREQ_FIRST_CHAR;
            if (RangeScaleFirstChar[3][j1] > FREQ_FIRST_CHAR_BOT)
              rescaleFirstChar(3, j1);
          }
        } while (j1--);
        j1 = 0x80;
        do {
          SymbolFirstChar[0][BaseSymbol][j1] = j1;
          SymbolFirstChar[1][BaseSymbol][j1] = j1;
          SymbolFirstChar[2][BaseSymbol][j1] = j1;
          SymbolFirstChar[3][BaseSymbol][j1] = j1;
          if (RangeScaleFirstChar[0][j1] || (j1 == BaseSymbol)) {
            FreqFirstChar[0][BaseSymbol][j1] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[0][BaseSymbol] += UP_FREQ_FIRST_CHAR;
          }
          if (RangeScaleFirstChar[1][j1] || (j1 == BaseSymbol)) {
            FreqFirstChar[1][BaseSymbol][j1] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[1][BaseSymbol] += UP_FREQ_FIRST_CHAR;
          }
          if (RangeScaleFirstChar[2][j1] || (j1 == BaseSymbol)) {
            FreqFirstChar[2][BaseSymbol][j1] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[2][BaseSymbol] += UP_FREQ_FIRST_CHAR;
          }
          if (RangeScaleFirstChar[3][j1] || (j1 == BaseSymbol)) {
            FreqFirstChar[3][BaseSymbol][j1] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[3][BaseSymbol] += UP_FREQ_FIRST_CHAR;
          }
        } while (j1--);
      }
      else if (RangeScaleFirstChar[0][0x80] == 0) {
        unsigned char j1 = 0x7F;
        do {
          if (RangeScaleFirstChar[0][j1]) {
            FreqFirstChar[0][j1][0x80] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[0][j1] += UP_FREQ_FIRST_CHAR;
            if (RangeScaleFirstChar[0][j1] > FREQ_FIRST_CHAR_BOT)
              rescaleFirstChar(0, j1);
          }
          if (RangeScaleFirstChar[1][j1]) {
            FreqFirstChar[1][j1][0x80] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[1][j1] += UP_FREQ_FIRST_CHAR;
            if (RangeScaleFirstChar[1][j1] > FREQ_FIRST_CHAR_BOT)
              rescaleFirstChar(1, j1);
          }
          if (RangeScaleFirstChar[2][j1]) {
            FreqFirstChar[2][j1][0x80] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[2][j1] += UP_FREQ_FIRST_CHAR;
            if (RangeScaleFirstChar[2][j1] > FREQ_FIRST_CHAR_BOT)
              rescaleFirstChar(2, j1);
          }
          if (RangeScaleFirstChar[3][j1]) {
            FreqFirstChar[3][j1][0x80] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[3][j1] += UP_FREQ_FIRST_CHAR;
            if (RangeScaleFirstChar[3][j1] > FREQ_FIRST_CHAR_BOT)
              rescaleFirstChar(3, j1);
          }
        } while (j1--);
        j1 = 0x80;
        do {
          SymbolFirstChar[0][0x80][j1] = j1;
          SymbolFirstChar[1][0x80][j1] = j1;
          SymbolFirstChar[2][0x80][j1] = j1;
          SymbolFirstChar[3][0x80][j1] = j1;
          if (RangeScaleFirstChar[0][j1]) {
            FreqFirstChar[0][0x80][j1] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[0][0x80] += UP_FREQ_FIRST_CHAR;
          }
          if (RangeScaleFirstChar[1][j1]) {
            FreqFirstChar[1][0x80][j1] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[1][0x80] += UP_FREQ_FIRST_CHAR;
          }
          if (RangeScaleFirstChar[2][j1]) {
            FreqFirstChar[2][0x80][j1] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[2][0x80] += UP_FREQ_FIRST_CHAR;
          }
          if (RangeScaleFirstChar[3][j1]) {
            FreqFirstChar[3][0x80][j1] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[3][0x80] += UP_FREQ_FIRST_CHAR;
          }
        } while (j1--);
        FreqFirstChar[0][0x80][0x80] = UP_FREQ_FIRST_CHAR;
        FreqFirstChar[1][0x80][0x80] = UP_FREQ_FIRST_CHAR;
        FreqFirstChar[2][0x80][0x80] = UP_FREQ_FIRST_CHAR;
        FreqFirstChar[3][0x80][0x80] = UP_FREQ_FIRST_CHAR;
        RangeScaleFirstChar[0][0x80] += UP_FREQ_FIRST_CHAR;
        RangeScaleFirstChar[1][0x80] += UP_FREQ_FIRST_CHAR;
        RangeScaleFirstChar[2][0x80] += UP_FREQ_FIRST_CHAR;
        RangeScaleFirstChar[3][0x80] += UP_FREQ_FIRST_CHAR;
      }
      if (BaseSymbol < START_UTF8_2BYTE_symbols) {
        symbol_data[num_symbols_defined].starts = symbol_data[num_symbols_defined].ends = prior_end = (unsigned char)BaseSymbol;
        *end_define_string_ptr++ = prior_end;
      }
      else {
        symbol_data[num_symbols_defined].starts = symbol_data[num_symbols_defined].ends = prior_end = 0x80;
        if (BaseSymbol < START_UTF8_3BYTE_symbols) {
          *end_define_string_ptr++ = (unsigned char)(BaseSymbol >> 6) + 0xC0;
          *end_define_string_ptr++ = (unsigned char)(BaseSymbol & 0x3F) + 0x80;
        }
        else if (BaseSymbol < START_UTF8_4BYTE_symbols) {
          *end_define_string_ptr++ = (unsigned char)(BaseSymbol >> 12) + 0xE0;
          *end_define_string_ptr++ = (unsigned char)((BaseSymbol >> 6) & 0x3F) + 0x80;
          *end_define_string_ptr++ = (unsigned char)(BaseSymbol & 0x3F) + 0x80;
        }
        else {
          *end_define_string_ptr++ = (unsigned char)(BaseSymbol >> 18) + 0xF0;
          *end_define_string_ptr++ = (unsigned char)((BaseSymbol >> 12) & 0x3F) + 0x80;
          *end_define_string_ptr++ = (unsigned char)((BaseSymbol >> 6) & 0x3F) + 0x80;
          *end_define_string_ptr++ = (unsigned char)(BaseSymbol & 0x3F) + 0x80;
        }
      }
    }
    else {
      unsigned char j1 = 0xFF;
      do {
        if (RangeScaleFirstChar[0][j1]) {
          FreqFirstCharBinary[j1][BaseSymbol] = UP_FREQ_FIRST_CHAR;
          RangeScaleFirstChar[0][j1] += UP_FREQ_FIRST_CHAR;
          if (BaseSymbol < 0x80) {
            RangeScaleFirstCharSection[j1][3] += UP_FREQ_FIRST_CHAR;
            if (BaseSymbol < 0x40) {
              RangeScaleFirstCharSection[j1][1] += UP_FREQ_FIRST_CHAR;
              if (BaseSymbol < 0x20)
                RangeScaleFirstCharSection[j1][0] += UP_FREQ_FIRST_CHAR;
            }
            else if (BaseSymbol < 0x60)
              RangeScaleFirstCharSection[j1][2] += UP_FREQ_FIRST_CHAR;
          }
          else if (BaseSymbol < 0xC0) {
            RangeScaleFirstCharSection[j1][5] += UP_FREQ_FIRST_CHAR;
            if (BaseSymbol < 0xA0)
              RangeScaleFirstCharSection[j1][4] += UP_FREQ_FIRST_CHAR;
          }
          else if (BaseSymbol < 0xE0)
            RangeScaleFirstCharSection[j1][6] += UP_FREQ_FIRST_CHAR;
          if (RangeScaleFirstChar[0][j1] > FREQ_FIRST_CHAR_BOT)
            rescaleFirstCharBinary(j1);
        }
      } while (j1--);
      j1 = 0xFF;
      do {
        SymbolFirstChar[0][BaseSymbol][j1] = j1;
        if (RangeScaleFirstChar[0][j1] || (j1 == BaseSymbol)) {
          FreqFirstCharBinary[BaseSymbol][j1] = UP_FREQ_FIRST_CHAR;
          RangeScaleFirstChar[0][BaseSymbol] += UP_FREQ_FIRST_CHAR;
          if (j1 < 0x80) {
            RangeScaleFirstCharSection[BaseSymbol][3] += UP_FREQ_FIRST_CHAR;
            if (j1 < 0x40) {
              RangeScaleFirstCharSection[BaseSymbol][1] += UP_FREQ_FIRST_CHAR;
              if (j1 < 0x20)
                RangeScaleFirstCharSection[BaseSymbol][0] += UP_FREQ_FIRST_CHAR;
            }
            else if (j1 < 0x60)
              RangeScaleFirstCharSection[BaseSymbol][2] += UP_FREQ_FIRST_CHAR;
          }
          else if (j1 < 0xC0) {
            RangeScaleFirstCharSection[BaseSymbol][5] += UP_FREQ_FIRST_CHAR;
            if (j1 < 0xA0)
              RangeScaleFirstCharSection[BaseSymbol][4] += UP_FREQ_FIRST_CHAR;
          }
          else if (j1 < 0xE0)
            RangeScaleFirstCharSection[BaseSymbol][6] += UP_FREQ_FIRST_CHAR;
        }
      } while (j1--);
      symbol_data[num_symbols_defined].starts = symbol_data[num_symbols_defined].ends = prior_end = (unsigned char)BaseSymbol;
      *end_define_string_ptr++ = prior_end;
    }

    if (find_first_symbol) {
      find_first_symbol = 0;
      end_symbol = prior_end;
      sym_list_ptrs[prior_end][max_code_length][0] = MAX_SYMBOLS_DEFINED - 1;
      nsob[prior_end][max_code_length] = 1;
      if (max_code_length >= 12) {
        bin_bits_under_max[prior_end] = max_code_length;
        sum_nbob[prior_end] = nbob[prior_end][max_code_length] = 1;
      }
      else
        sum_nbob[prior_end] = nbob[prior_end][max_code_length] = 1 << (12 - max_code_length);
    }
    if (define_symbol_instances == 1) {
      symbol_number = num_symbols_defined;
      symbol_string_ptr = symbol_strings + symbol_data[num_symbols_defined].string_index;
      define_string_ptr = define_string;
      while (define_string_ptr != end_define_string_ptr)
        *symbol_string_ptr++ = *define_string_ptr++;
      symbol_data[++num_symbols_defined].string_index = symbol_string_ptr - symbol_strings;
      return(end_define_string_ptr);
    }
  }
  else {
    DecodeSIDFinish(NOT_CAP);
    symbols_in_definition = SIDSymbol + 1;
    if (symbols_in_definition == 16) {
      get_extra_length();
    }
    DecodeINSTStart(NOT_CAP);
    if (DecodeINSTCheck0(NOT_CAP)) {
      DecodeINSTFinish0(NOT_CAP);
      define_symbol_instances = 2;
      define_symbol_code_length = max_code_length;
    }
    else {
      DecodeINSTFinish(NOT_CAP);
      if (Instances >= MAX_INSTANCES_FOR_MTF_QUEUE) {
        define_symbol_instances = 0;
        define_symbol_code_length = max_regular_code_length + MAX_INSTANCES_FOR_MTF_QUEUE - Instances;
      }
      else {
        define_symbol_instances = Instances + 2;
        define_symbol_code_length = mtf_queue_miss_code_length[define_symbol_instances];
      }
    }

    do { // Build the symbol string from the next symbols_in_definition symbols
      DecodeSymTypeStart(LEVEL1);
      if (DecodeSymTypeCheckType0(LEVEL1)) {
        DecodeSymTypeFinishType0(LEVEL1);
        if (UTF8_compliant) {
          DecodeFirstChar(0, prior_end);
        }
        else {
          DecodeFirstCharBinary(prior_end);
        }
        DictionaryBins = sum_nbob[FirstChar];
        DecodeDictionaryBin(lookup_bits[FirstChar]);
        if (CodeLength > bin_bits_under_max[FirstChar]) {
          get_long_symbol();
        }
        else {
          get_short_symbol();
        }
        if (symbol_data[symbol_number].instances <= MAX_INSTANCES_FOR_MTF_QUEUE) {
          if (use_mtf) {
            insert_mtf_queue(NOT_CAP);
          }
          else if (--symbol_data[symbol_number].remaining == 0) {
            remove_dictionary_symbol(symbol_number,CodeLength);
          }
        }
        else if (symbol_data[symbol_number].type & 4) {
          add_new_symbol_to_mtfg_queue(symbol_number);
        }
        prior_end = symbol_data[symbol_number].ends;
        symbol_string_ptr = symbol_strings + symbol_data[symbol_number].string_index;
        next_string_ptr = symbol_strings + symbol_data[symbol_number + 1].string_index;
        while (symbol_string_ptr != next_string_ptr)
          *end_define_string_ptr++ = *symbol_string_ptr++;
      }
      else if (DecodeSymTypeCheckType1(LEVEL1)) {
        DecodeSymTypeFinishType1(LEVEL1);
        end_define_string_ptr = decode_define(end_define_string_ptr);
      }
      else {
        if (DecodeSymTypeCheckType2(LEVEL1)) {
          DecodeSymTypeFinishType2(LEVEL1);
          get_mtfg_symbol();
        }
        else {
          DecodeSymTypeFinishType3(LEVEL1);
          get_mtf_symbol();
        }
        prior_end = symbol_data[symbol_number].ends;
        symbol_string_ptr = symbol_strings + symbol_data[symbol_number].string_index;
        next_string_ptr = symbol_strings + symbol_data[symbol_number + 1].string_index;
        while (symbol_string_ptr != next_string_ptr)
          *end_define_string_ptr++ = *symbol_string_ptr++;
      }
    } while (--symbols_in_definition);
    if (*define_string < 0x80)
      symbol_data[num_symbols_defined].starts = *define_string;
    else if (UTF8_compliant)
      symbol_data[num_symbols_defined].starts = 0x80;
    else
      symbol_data[num_symbols_defined].starts = *define_string;
    symbol_data[num_symbols_defined].ends = prior_end;
  }

  if (define_symbol_instances) { // mtf queue symbol
    if (define_symbol_instances == 2) {
      symbol_data[num_symbols_defined].instances = 2;
      symbol_data[num_symbols_defined].remaining = 1;
      if (use_mtf) {
        mtf_queue_number = 0; // WHY SET THIS? !!!
        UpFreqMtfQueueNumD(NOT_CAP);
        if (mtf_queue_size[2] != MTF_QUEUE_SIZE) // put the symbol in the mtf queue
          mtf_queue[2][(mtf_queue_size[2]++ + mtf_queue_offset[2]) & 0x3F] = num_symbols_defined;
        else { // put last mtf queue symbol in symbol list
          symbol_number = *(mtf_queue_ptr = &mtf_queue[2][mtf_queue_offset[2]++ & 0x3F]);
          add_dictionary_symbol(symbol_number,define_symbol_code_length);
          // put symbol in queue and rotate cyclical buffer
          *mtf_queue_ptr = num_symbols_defined;
        }
      }
      else {
        add_dictionary_symbol(num_symbols_defined,define_symbol_code_length);
      }
    }
    else {
      symbol_data[num_symbols_defined].instances = define_symbol_instances;
      symbol_data[num_symbols_defined].remaining = define_symbol_instances - 1;
      if (use_mtf) {
        mtf_queue_number = define_symbol_instances - 2;
        UpFreqMtfQueueNumD(NOT_CAP);
        if (mtf_queue_size[define_symbol_instances] != MTF_QUEUE_SIZE) // put the symbol in the mtf queue
          mtf_queue[define_symbol_instances]
                [(mtf_queue_size[define_symbol_instances]++ + mtf_queue_offset[define_symbol_instances]) & 0x3F]
              = num_symbols_defined;
        else { // put last mtf queue symbol in symbol list
          symbol_number
              = *(mtf_queue_ptr = &mtf_queue[define_symbol_instances][mtf_queue_offset[define_symbol_instances]++ & 0x3F]);
          add_dictionary_symbol(symbol_number,define_symbol_code_length);
          // put symbol in queue and rotate cyclical buffer
          *mtf_queue_ptr = num_symbols_defined;
        }
      }
      else {
        add_dictionary_symbol(num_symbols_defined,define_symbol_code_length);
      }
    }
  }
  else { // put symbol in table
    if ((define_symbol_code_length > 10) && use_mtf) {
      unsigned char nonergodic;
      DecodeERG(0);
      if (nonergodic) {
        symbol_data[num_symbols_defined].type = 4;
        add_new_symbol_to_mtfg_queue(num_symbols_defined);
      }
    }
    symbol_data[num_symbols_defined].instances = MAX_INSTANCES_FOR_MTF_QUEUE + define_symbol_code_length;
    add_dictionary_symbol(num_symbols_defined,define_symbol_code_length);
  }
  symbol_number = num_symbols_defined;
  symbol_string_ptr = symbol_strings + symbol_data[num_symbols_defined].string_index;
  define_string_ptr = define_string;
  copy_string(define_string_ptr, end_define_string_ptr, symbol_string_ptr);
  symbol_data[++num_symbols_defined].string_index = symbol_string_ptr - symbol_strings;
  return(end_define_string_ptr);
}


unsigned char* decode_define_cap_encoded(unsigned char* define_string, unsigned char first_char_needs_cap) {
  unsigned char define_symbol_instances, define_symbol_code_length, *define_string_ptr, *end_define_string_ptr;
  unsigned char char_before_define_is_cap;
  unsigned int symbols_in_definition;
  unsigned char tag_type = 0;

  char_before_define_is_cap = prior_is_cap;
  caps_on = 0;
  end_define_string_ptr = define_string;

  DecodeSIDStart(prior_is_cap);
  if (DecodeSIDCheck0(prior_is_cap)) {
    DecodeSIDFinish0(prior_is_cap);
    DecodeINSTStart(prior_is_cap);
    if (DecodeINSTCheck0(prior_is_cap)) {
      DecodeINSTFinish0(prior_is_cap);
      define_symbol_instances = 2;
      define_symbol_code_length = max_code_length;
    }
    else {
      DecodeINSTFinish(prior_is_cap);
      if (Instances >= MAX_INSTANCES_FOR_MTF_QUEUE) {
        define_symbol_instances = 0;
        define_symbol_code_length = max_regular_code_length + MAX_INSTANCES_FOR_MTF_QUEUE - Instances;
      }
      else if (Instances != MAX_INSTANCES_FOR_MTF_QUEUE - 1) {
        define_symbol_instances = Instances + 2;
        define_symbol_code_length = mtf_queue_miss_code_length[define_symbol_instances];
      }
      else
        define_symbol_instances = 1;
    }

    DecodeBaseSymbol(base_bits);
    if (UTF8_compliant) {
      if (BaseSymbol < 0x80) {
        unsigned char j1 = 0x80;
        do {
          if (RangeScaleFirstChar[0][j1]) {
            unsigned char j2 = 0x80;
            while (SymbolFirstChar[0][j1][j2] != (unsigned char)BaseSymbol)
              j2--;
            FreqFirstChar[0][j1][j2] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[0][j1] += UP_FREQ_FIRST_CHAR;
            if (RangeScaleFirstChar[0][j1] > FREQ_FIRST_CHAR_BOT)
              rescaleFirstChar(0, j1);
          }
          if (RangeScaleFirstChar[1][j1]) {
            unsigned char j2 = 0x80;
            while (SymbolFirstChar[1][j1][j2] != (unsigned char)BaseSymbol)
              j2--;
            FreqFirstChar[1][j1][j2] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[1][j1] += UP_FREQ_FIRST_CHAR;
            if (RangeScaleFirstChar[1][j1] > FREQ_FIRST_CHAR_BOT)
              rescaleFirstChar(1, j1);
          }
          if (RangeScaleFirstChar[2][j1]) {
            unsigned char j2 = 0x80;
            while (SymbolFirstChar[2][j1][j2] != (unsigned char)BaseSymbol)
              j2--;
            FreqFirstChar[2][j1][j2] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[2][j1] += UP_FREQ_FIRST_CHAR;
            if (RangeScaleFirstChar[2][j1] > FREQ_FIRST_CHAR_BOT)
              rescaleFirstChar(2, j1);
          }
          if (RangeScaleFirstChar[3][j1]) {
            unsigned char j2 = 0x80;
            while (SymbolFirstChar[3][j1][j2] != (unsigned char)BaseSymbol)
              j2--;
            FreqFirstChar[3][j1][j2] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[3][j1] += UP_FREQ_FIRST_CHAR;
            if (RangeScaleFirstChar[3][j1] > FREQ_FIRST_CHAR_BOT)
              rescaleFirstChar(3, j1);
          }
        } while (j1--);
        j1 = 0x80;
        do {
          SymbolFirstChar[0][BaseSymbol][j1] = j1;
          SymbolFirstChar[1][BaseSymbol][j1] = j1;
          SymbolFirstChar[2][BaseSymbol][j1] = j1;
          SymbolFirstChar[3][BaseSymbol][j1] = j1;
          if (RangeScaleFirstChar[0][j1] || (j1 == BaseSymbol)) {
            FreqFirstChar[0][BaseSymbol][j1] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[0][BaseSymbol] += UP_FREQ_FIRST_CHAR;
          }
          if (RangeScaleFirstChar[1][j1] || (j1 == BaseSymbol)) {
            FreqFirstChar[1][BaseSymbol][j1] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[1][BaseSymbol] += UP_FREQ_FIRST_CHAR;
          }
          if (RangeScaleFirstChar[2][j1] || (j1 == BaseSymbol)) {
            FreqFirstChar[2][BaseSymbol][j1] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[2][BaseSymbol] += UP_FREQ_FIRST_CHAR;
          }
          if (RangeScaleFirstChar[3][j1] || (j1 == BaseSymbol)) {
            FreqFirstChar[3][BaseSymbol][j1] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[3][BaseSymbol] += UP_FREQ_FIRST_CHAR;
          }
        } while (j1--);
      }
      else if (RangeScaleFirstChar[0][0x80] == 0) {
        unsigned char j1 = 0x7F;
        do {
          if (RangeScaleFirstChar[0][j1]) {
            FreqFirstChar[0][j1][0x80] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[0][j1] += UP_FREQ_FIRST_CHAR;
            if (RangeScaleFirstChar[0][j1] > FREQ_FIRST_CHAR_BOT)
              rescaleFirstChar(0, j1);
          }
          if (RangeScaleFirstChar[1][j1]) {
            FreqFirstChar[1][j1][0x80] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[1][j1] += UP_FREQ_FIRST_CHAR;
            if (RangeScaleFirstChar[1][j1] > FREQ_FIRST_CHAR_BOT)
              rescaleFirstChar(1, j1);
          }
          if (RangeScaleFirstChar[2][j1]) {
            FreqFirstChar[2][j1][0x80] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[2][j1] += UP_FREQ_FIRST_CHAR;
            if (RangeScaleFirstChar[2][j1] > FREQ_FIRST_CHAR_BOT)
              rescaleFirstChar(2, j1);
          }
          if (RangeScaleFirstChar[3][j1]) {
            FreqFirstChar[3][j1][0x80] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[3][j1] += UP_FREQ_FIRST_CHAR;
            if (RangeScaleFirstChar[3][j1] > FREQ_FIRST_CHAR_BOT)
              rescaleFirstChar(3, j1);
          }
        } while (j1--);
        j1 = 0x80;
        do {
          SymbolFirstChar[0][0x80][j1] = j1;
          SymbolFirstChar[1][0x80][j1] = j1;
          SymbolFirstChar[2][0x80][j1] = j1;
          SymbolFirstChar[3][0x80][j1] = j1;
          if (RangeScaleFirstChar[0][j1]) {
            FreqFirstChar[0][0x80][j1] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[0][0x80] += UP_FREQ_FIRST_CHAR;
          }
          if (RangeScaleFirstChar[1][j1]) {
            FreqFirstChar[1][0x80][j1] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[1][0x80] += UP_FREQ_FIRST_CHAR;
          }
          if (RangeScaleFirstChar[2][j1]) {
            FreqFirstChar[2][0x80][j1] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[2][0x80] += UP_FREQ_FIRST_CHAR;
          }
          if (RangeScaleFirstChar[3][j1]) {
            FreqFirstChar[3][0x80][j1] = UP_FREQ_FIRST_CHAR;
            RangeScaleFirstChar[3][0x80] += UP_FREQ_FIRST_CHAR;
          }
        } while (j1--);
        FreqFirstChar[0][0x80][0x80] = UP_FREQ_FIRST_CHAR;
        FreqFirstChar[1][0x80][0x80] = UP_FREQ_FIRST_CHAR;
        FreqFirstChar[2][0x80][0x80] = UP_FREQ_FIRST_CHAR;
        FreqFirstChar[3][0x80][0x80] = UP_FREQ_FIRST_CHAR;
        RangeScaleFirstChar[0][0x80] += UP_FREQ_FIRST_CHAR;
        RangeScaleFirstChar[1][0x80] += UP_FREQ_FIRST_CHAR;
        RangeScaleFirstChar[2][0x80] += UP_FREQ_FIRST_CHAR;
        RangeScaleFirstChar[3][0x80] += UP_FREQ_FIRST_CHAR;
      }
    }
    else {
      unsigned char j1 = 0xFF;
      do {
        if (RangeScaleFirstChar[0][j1]) {
          unsigned char j2 = 0xFF;
          while (SymbolFirstChar[0][j1][j2] != (unsigned char)BaseSymbol)
            j2--;
          FreqFirstChar[0][j1][j2] = UP_FREQ_FIRST_CHAR;
          RangeScaleFirstChar[0][j1] += UP_FREQ_FIRST_CHAR;
          if (RangeScaleFirstChar[0][j1] > FREQ_FIRST_CHAR_BOT)
            rescaleFirstChar(0, j1);
        }
        if (RangeScaleFirstChar[1][j1]) {
          unsigned char j2 = 0xFF;
          while (SymbolFirstChar[1][j1][j2] != (unsigned char)BaseSymbol)
            j2--;
          FreqFirstChar[1][j1][j2] = UP_FREQ_FIRST_CHAR;
          RangeScaleFirstChar[1][j1] += UP_FREQ_FIRST_CHAR;
          if (RangeScaleFirstChar[1][j1] > FREQ_FIRST_CHAR_BOT)
            rescaleFirstChar(1, j1);
        }
        if (RangeScaleFirstChar[2][j1]) {
          unsigned char j2 = 0xFF;
          while (SymbolFirstChar[2][j1][j2] != (unsigned char)BaseSymbol)
            j2--;
          FreqFirstChar[2][j1][j2] = UP_FREQ_FIRST_CHAR;
          RangeScaleFirstChar[2][j1] += UP_FREQ_FIRST_CHAR;
          if (RangeScaleFirstChar[2][j1] > FREQ_FIRST_CHAR_BOT)
            rescaleFirstChar(2, j1);
        }
        if (RangeScaleFirstChar[3][j1]) {
          unsigned char j2 = 0xFF;
          while (SymbolFirstChar[3][j1][j2] != (unsigned char)BaseSymbol)
            j2--;
          FreqFirstChar[3][j1][j2] = UP_FREQ_FIRST_CHAR;
          RangeScaleFirstChar[3][j1] += UP_FREQ_FIRST_CHAR;
          if (RangeScaleFirstChar[3][j1] > FREQ_FIRST_CHAR_BOT)
            rescaleFirstChar(3, j1);
        }
      } while (j1--);
      j1 = 0xFF;
      do {
        SymbolFirstChar[0][BaseSymbol][j1] = j1;
        SymbolFirstChar[1][BaseSymbol][j1] = j1;
        SymbolFirstChar[2][BaseSymbol][j1] = j1;
        SymbolFirstChar[3][BaseSymbol][j1] = j1;
        if (RangeScaleFirstChar[0][j1] || (j1 == BaseSymbol)) {
          FreqFirstChar[0][BaseSymbol][j1] = UP_FREQ_FIRST_CHAR;
          RangeScaleFirstChar[0][BaseSymbol] += UP_FREQ_FIRST_CHAR;
        }
        if (RangeScaleFirstChar[1][j1] || (j1 == BaseSymbol)) {
          FreqFirstChar[1][BaseSymbol][j1] = UP_FREQ_FIRST_CHAR;
          RangeScaleFirstChar[1][BaseSymbol] += UP_FREQ_FIRST_CHAR;
        }
        if (RangeScaleFirstChar[2][j1] || (j1 == BaseSymbol)) {
          FreqFirstChar[2][BaseSymbol][j1] = UP_FREQ_FIRST_CHAR;
          RangeScaleFirstChar[2][BaseSymbol] += UP_FREQ_FIRST_CHAR;
        }
        if (RangeScaleFirstChar[3][j1] || (j1 == BaseSymbol)) {
          FreqFirstChar[3][BaseSymbol][j1] = UP_FREQ_FIRST_CHAR;
          RangeScaleFirstChar[3][BaseSymbol] += UP_FREQ_FIRST_CHAR;
        }
      } while (j1--);
    }

    if (BaseSymbol < START_UTF8_2BYTE_symbols) {
      symbol_data[num_symbols_defined].starts = symbol_data[num_symbols_defined].ends = (unsigned char)BaseSymbol;
      if (BaseSymbol == CAP_CHAR) {
        symbol_data[num_symbols_defined].type = 1;
        caps_on = 1;
        prior_is_cap = 1;
      }
      else {
        symbol_data[num_symbols_defined].type = ((BaseSymbol >= 0x61) && (BaseSymbol <= 0x7A)) << 1;
        *end_define_string_ptr++ = (unsigned char)BaseSymbol;
        prior_is_cap = 0;
      }
    }
    else {
      symbol_data[num_symbols_defined].type = 0;
      prior_is_cap = 0;
      if (UTF8_compliant) {
        symbol_data[num_symbols_defined].starts = symbol_data[num_symbols_defined].ends = 0x80;
        if (BaseSymbol < START_UTF8_3BYTE_symbols) {
          *end_define_string_ptr++ = (unsigned char)(BaseSymbol >> 6) + 0xC0;
          *end_define_string_ptr++ = (unsigned char)(BaseSymbol & 0x3F) + 0x80;
        }
        else if (BaseSymbol < START_UTF8_4BYTE_symbols) {
          *end_define_string_ptr++ = (unsigned char)(BaseSymbol >> 12) + 0xE0;
          *end_define_string_ptr++ = (unsigned char)((BaseSymbol >> 6) & 0x3F) + 0x80;
          *end_define_string_ptr++ = (unsigned char)(BaseSymbol & 0x3F) + 0x80;
        }
        else {
          *end_define_string_ptr++ = (unsigned char)(BaseSymbol >> 18) + 0xF0;
          *end_define_string_ptr++ = (unsigned char)((BaseSymbol >> 12) & 0x3F) + 0x80;
          *end_define_string_ptr++ = (unsigned char)((BaseSymbol >> 6) & 0x3F) + 0x80;
          *end_define_string_ptr++ = (unsigned char)(BaseSymbol & 0x3F) + 0x80;
        }
      }
      else {
        symbol_data[num_symbols_defined].starts = symbol_data[num_symbols_defined].ends = (unsigned char)BaseSymbol;
        *end_define_string_ptr++ = (unsigned char)BaseSymbol;
      }
    }
    if (UTF8_compliant && (BaseSymbol > 0x80))
      prior_end = 0x80;
    else
      prior_end = (unsigned char)BaseSymbol;
    if (find_first_symbol) {
      find_first_symbol = 0;
      end_symbol = prior_end;
      sym_list_ptrs[prior_end][max_code_length][0] = MAX_SYMBOLS_DEFINED - 1;
      nsob[prior_end][max_code_length] = 1;
      if (max_code_length >= 12) {
        bin_bits_under_max[prior_end] = max_code_length;
        sum_nbob[prior_end] = nbob[prior_end][max_code_length] = 1;
      }
      else
        sum_nbob[prior_end] = nbob[prior_end][max_code_length] = 1 << (12 - max_code_length);
    }
    if (define_symbol_instances == 1) {
      symbol_string_ptr = symbol_strings + symbol_data[num_symbols_defined].string_index;
      define_string_ptr = define_string;
      while (define_string_ptr != end_define_string_ptr)
        *symbol_string_ptr++ = *define_string_ptr++;
      if ((BaseSymbol == (unsigned int)' ') || (BaseSymbol == CAP_CHAR))
        symbol_data[num_symbols_defined].type |= 0x10;
      symbol_number = num_symbols_defined;
      symbol_data[++num_symbols_defined].string_index = symbol_string_ptr - symbol_strings;
      return(end_define_string_ptr);
    }
    if (BaseSymbol != CAP_CHAR) {
      symbol_string_ptr = symbol_strings + symbol_data[num_symbols_defined].string_index;
      define_string_ptr = define_string;
      copy_string(define_string_ptr, end_define_string_ptr, symbol_string_ptr);
      symbol_data[num_symbols_defined+1].string_index = symbol_string_ptr - symbol_strings;
      if (char_before_define_is_cap && first_char_needs_cap)
        *define_string -= 0x20;
      if (BaseSymbol == (unsigned int)' ')
        symbol_data[num_symbols_defined].type |= 0x10;
    }
    else {
      symbol_data[num_symbols_defined+1].string_index = symbol_data[num_symbols_defined].string_index;
      symbol_data[num_symbols_defined].type |= 0x10;
    }
  }
  else {
    DecodeSIDFinish(prior_is_cap);
    if ((symbols_in_definition = SIDSymbol + 1) == 16) {
      get_extra_length();
    }
    DecodeINSTStart(prior_is_cap);
    if (DecodeINSTCheck0(prior_is_cap)) {
      DecodeINSTFinish0(prior_is_cap);
      define_symbol_instances = 2;
      define_symbol_code_length = max_code_length;
    }
    else {
      DecodeINSTFinish(prior_is_cap);
      if (Instances >= MAX_INSTANCES_FOR_MTF_QUEUE) {
        define_symbol_instances = 0;
        define_symbol_code_length = max_regular_code_length + MAX_INSTANCES_FOR_MTF_QUEUE - Instances;
      }
      else {
        define_symbol_instances = Instances + 2;
        define_symbol_code_length = mtf_queue_miss_code_length[define_symbol_instances];
      }
    }

    do { // Build the symbol string from the next symbols_in_definition symbols
      if (prior_is_cap == 0) {
        DecodeSymTypeStart(LEVEL1);
        if (DecodeSymTypeCheckType0(LEVEL1)) {
          DecodeSymTypeFinishType0(LEVEL1);
          if (symbol_data[symbol_number].type & 0x20) {
            if (symbol_data[symbol_number].type & 0x80) {
              DecodeFirstChar(2, prior_end);
            }
            else if (symbol_data[symbol_number].type & 0x40) {
              DecodeFirstChar(3, prior_end);
            }
            else {
              DecodeFirstChar(1, prior_end);
            }
          }
          else {
            DecodeFirstChar(0, prior_end);
          }
          DictionaryBins = sum_nbob[FirstChar];
          DecodeDictionaryBin(lookup_bits[FirstChar]);
          if (CodeLength > bin_bits_under_max[FirstChar]) {
            get_long_symbol();
          }
          else {
            get_short_symbol();
          }
          if (symbol_data[symbol_number].instances <= MAX_INSTANCES_FOR_MTF_QUEUE) {
            if (use_mtf) {
              insert_mtf_queue(NOT_CAP);
            }
            else if (--symbol_data[symbol_number].remaining == 0) {
              remove_dictionary_symbol(symbol_number,CodeLength);
            }
          }
          else if (symbol_data[symbol_number].type & 4) {
            add_new_symbol_to_mtfg_queue(symbol_number);
          }
          prior_end = symbol_data[symbol_number].ends;
          symbol_string_ptr = symbol_strings + symbol_data[symbol_number].string_index;
          next_string_ptr = symbol_strings + symbol_data[symbol_number + 1].string_index;
          while (symbol_string_ptr != next_string_ptr)
            *end_define_string_ptr++ = *symbol_string_ptr++;
          caps_on = symbol_data[symbol_number].type & 1;
          prior_is_cap = caps_on;
        }
        else if (DecodeSymTypeCheckType1(LEVEL1)) {
          DecodeSymTypeFinishType1(LEVEL1);
          end_define_string_ptr = decode_define_cap_encoded(end_define_string_ptr,caps_on);
        }
        else {
          if (DecodeSymTypeCheckType2(LEVEL1)) {
            DecodeSymTypeFinishType2(LEVEL1);
            get_mtfg_symbol();
          }
          else {
            DecodeSymTypeFinishType3(LEVEL1);
            get_mtf_symbol();
          }
          prior_end = symbol_data[symbol_number].ends;
          symbol_string_ptr = symbol_strings + symbol_data[symbol_number].string_index;
          next_string_ptr = symbol_strings + symbol_data[symbol_number + 1].string_index;
          while (symbol_string_ptr != next_string_ptr)
            *end_define_string_ptr++ = *symbol_string_ptr++;
          caps_on = symbol_data[symbol_number].type & 1;
          prior_is_cap = caps_on;
        }
      }
      else { // prior_is_cap
        DecodeSymTypeStart(LEVEL1_CAP);
        if (DecodeSymTypeCheckType0(LEVEL1_CAP)) {
          DecodeSymTypeFinishType0(LEVEL1_CAP);
          if (symbol_data[symbol_number].type & 0x20) {
            if (symbol_data[symbol_number].type & 0x80) {
              DecodeFirstChar(2, prior_end);
            }
            else if (symbol_data[symbol_number].type & 0x40) {
              DecodeFirstChar(3, prior_end);
            }
            else {
              DecodeFirstChar(1, prior_end);
            }
          }
          else {
            DecodeFirstChar(0, prior_end);
          }
          DictionaryBins = sum_nbob[FirstChar];
          DecodeDictionaryBin(lookup_bits[FirstChar]);
          if (CodeLength > bin_bits_under_max[FirstChar]) {
            get_long_symbol();
          }
          else {
            get_short_symbol();
          }
          if (symbol_data[symbol_number].instances <= MAX_INSTANCES_FOR_MTF_QUEUE) {
            if (use_mtf) {
              insert_mtf_queue(CAP);
            }
            else if (--symbol_data[symbol_number].remaining == 0) {
              remove_dictionary_symbol(symbol_number,CodeLength);
            }
          }
          else if (symbol_data[symbol_number].type & 4) {
            add_new_symbol_to_mtfg_queue(symbol_number);
          }
          prior_end = symbol_data[symbol_number].ends;
          symbol_string_ptr = symbol_strings + symbol_data[symbol_number].string_index;
          next_string_ptr = symbol_strings + symbol_data[symbol_number + 1].string_index;
          if (caps_on)
            *end_define_string_ptr++ = *symbol_string_ptr++ - 0x20;
          while (symbol_string_ptr != next_string_ptr)
            *end_define_string_ptr++ = *symbol_string_ptr++;
          caps_on = symbol_data[symbol_number].type & 1;
          prior_is_cap = caps_on;
        }
        else if (DecodeSymTypeCheckType1(LEVEL1_CAP)) {
          DecodeSymTypeFinishType1(LEVEL1_CAP);
          end_define_string_ptr = decode_define_cap_encoded(end_define_string_ptr,caps_on);
        }
        else {
          if (DecodeSymTypeCheckType2(LEVEL1_CAP)) {
            DecodeSymTypeFinishType2(LEVEL1_CAP);
            get_mtfg_symbol_cap();
          }
          else {
            DecodeSymTypeFinishType3(LEVEL1_CAP);
            get_mtf_symbol_cap();
          }
          prior_end = symbol_data[symbol_number].ends;
          symbol_string_ptr = symbol_strings + symbol_data[symbol_number].string_index;
          next_string_ptr = symbol_strings + symbol_data[symbol_number + 1].string_index;
          if (caps_on)
            *end_define_string_ptr++ = *symbol_string_ptr++ - 0x20;
          while (symbol_string_ptr != next_string_ptr)
            *end_define_string_ptr++ = *symbol_string_ptr++;
          caps_on = symbol_data[symbol_number].type & 1;
          prior_is_cap = caps_on;
        }
      }
    } while (--symbols_in_definition);
    symbol_data[num_symbols_defined].type = (((*define_string >= 'a') && (*define_string <= 'z')) << 1) + caps_on;
    if (*define_string < 0x80) {
      if ((*define_string > 0x40) && (*define_string < 0x5b))
        symbol_data[num_symbols_defined].starts = CAP_CHAR;
      else
        symbol_data[num_symbols_defined].starts = *define_string;
    }
    else if (UTF8_compliant)
      symbol_data[num_symbols_defined].starts = 0x80;
    else
      symbol_data[num_symbols_defined].starts = *define_string;
    symbol_data[num_symbols_defined].ends = prior_end;

    symbol_string_ptr = symbol_strings + symbol_data[num_symbols_defined].string_index;
    define_string_ptr = define_string;
    copy_string(define_string_ptr, end_define_string_ptr, symbol_string_ptr);
    symbol_data[num_symbols_defined+1].string_index = symbol_string_ptr - symbol_strings;
    if (char_before_define_is_cap && first_char_needs_cap)
      *define_string -= 0x20;

    if (symbol_data[symbol_number].type & 0x10) {
      symbol_data[num_symbols_defined].type |= symbol_data[symbol_number].type & 0x30;
      if (symbol_data[num_symbols_defined].type & 0x20) {
        if (symbol_data[symbol_number].type & 0x80)
          symbol_data[num_symbols_defined].type |= 0xC0;
        else if (define_symbol_instances == 0) {
          DecodeWordTag();
          tag_type = 1 + Symbol;
          symbol_data[num_symbols_defined].type |= 0x40 + (Symbol << 7);
        }
        else
          symbol_data[num_symbols_defined].type |= symbol_data[symbol_number].type & 0xC0;
      }
    }
    else {
      unsigned char * start_string_ptr = symbol_strings + symbol_data[num_symbols_defined].string_index;
      symbol_string_ptr--;
      if (((symbol_data[num_symbols_defined].type & 1) == 0) && (*symbol_string_ptr != (unsigned int)' ')) {
        while (symbol_string_ptr-- != start_string_ptr) {
          if (*symbol_string_ptr == (unsigned int)' ') {
            symbol_data[num_symbols_defined].type |= 0x30;
            if (define_symbol_instances == 0) {
              DecodeWordTag();
              tag_type = 1 + Symbol;
              symbol_data[num_symbols_defined].type |= 0x40 + (Symbol << 7);
            }
            break;
          }
        }
      }
      else
        symbol_data[num_symbols_defined].type |= 0x10;
    }
  }

  if (define_symbol_instances) { // mtf queue symbol
    if (define_symbol_instances == 2) {
      symbol_data[num_symbols_defined].instances = 2;
      symbol_data[num_symbols_defined].remaining = 1;
      if (use_mtf) {
        mtf_queue_number = 0;
        if (char_before_define_is_cap == 0) {
          UpFreqMtfQueueNumD(NOT_CAP);
        }
        else {
          UpFreqMtfQueueNumD(CAP);
        }
        if (mtf_queue_size[2] != MTF_QUEUE_SIZE) // put the symbol in the mtf queue
          mtf_queue[2][(mtf_queue_size[2]++ + mtf_queue_offset[2]) & 0x3F] = num_symbols_defined;
        else { // put last mtf queue symbol in symbol list
          symbol_number = *(mtf_queue_ptr = &mtf_queue[2][mtf_queue_offset[2]++ & 0x3F]);
          add_dictionary_symbol(symbol_number,define_symbol_code_length);
          // put symbol in queue and rotate cyclical buffer
          *mtf_queue_ptr = num_symbols_defined;
        }
      }
      else {
        add_dictionary_symbol(num_symbols_defined,define_symbol_code_length);
      }
    }
    else {
      symbol_data[num_symbols_defined].instances = define_symbol_instances;
      symbol_data[num_symbols_defined].remaining = define_symbol_instances - 1;
      if (use_mtf) {
        mtf_queue_number = define_symbol_instances - 2;
        if (char_before_define_is_cap == 0) {
          UpFreqMtfQueueNumD(NOT_CAP);
        }
        else {
          UpFreqMtfQueueNumD(CAP);
        }
        if (mtf_queue_size[define_symbol_instances] != MTF_QUEUE_SIZE) // put the symbol in the mtf queue
          mtf_queue[define_symbol_instances]
                [(mtf_queue_size[define_symbol_instances]++ + mtf_queue_offset[define_symbol_instances]) & 0x3F]
              = num_symbols_defined;
        else { // put last mtf queue symbol in symbol list
          symbol_number
              = *(mtf_queue_ptr = &mtf_queue[define_symbol_instances][mtf_queue_offset[define_symbol_instances]++ & 0x3F]);
          add_dictionary_symbol(symbol_number,define_symbol_code_length);
          // put symbol in queue and rotate cyclical buffer
          *mtf_queue_ptr = num_symbols_defined;
        }
      }
      else {
        add_dictionary_symbol(num_symbols_defined,define_symbol_code_length);
      }
    }
  }
  else { // put symbol in table
    if ((define_symbol_code_length > 10) && use_mtf) {
      unsigned char nonergodic;
      DecodeERG(tag_type);
      if (nonergodic) {
        symbol_data[num_symbols_defined].type |= 4;
        add_new_symbol_to_mtfg_queue(num_symbols_defined);
      }
    }
    symbol_data[num_symbols_defined].instances = MAX_INSTANCES_FOR_MTF_QUEUE + define_symbol_code_length;
    add_dictionary_symbol(num_symbols_defined,define_symbol_code_length);
  }
  symbol_number = num_symbols_defined++;
  return(end_define_string_ptr);
}


#define write_output_buffer() { \
  fflush(fd_out); \
  chars_to_write = out_char_ptr - start_char_ptr; \
  fwrite(start_char_ptr,1,chars_to_write,fd_out); \
  out_chars += chars_to_write; \
  if (out_buffer_num == 0) { \
    out_buffer_num = 1; \
    if (delta_gap) { \
      out_char1[0] = *(out_char_ptr-4); \
      out_char1[1] = *(out_char_ptr-3); \
      out_char1[2] = *(out_char_ptr-2); \
      out_char1[3] = *(out_char_ptr-1); \
    } \
    out_char_ptr = out_char1 + 4; \
    start_char_ptr = out_char_ptr; \
    extra_out_char_ptr = out_char_ptr + CHARS_TO_WRITE; \
  } \
  else { \
    out_buffer_num = 0; \
    if (delta_gap) { \
      out_char0[0] = *(out_char_ptr-4); \
      out_char0[1] = *(out_char_ptr-3); \
      out_char0[2] = *(out_char_ptr-2); \
      out_char0[3] = *(out_char_ptr-1); \
    } \
    out_char_ptr = out_char0 + 4; \
    start_char_ptr = out_char_ptr; \
    extra_out_char_ptr = out_char_ptr + CHARS_TO_WRITE; \
    if ((out_buffers_sent++ & 0x1F) == 0) \
      fprintf(stderr,"%u\r",out_chars); \
  } \
}


#define write_string() { \
  copy_string(symbol_string_ptr, next_symbol_string_ptr, out_char_ptr); \
  if (out_char_ptr >= extra_out_char_ptr) \
    write_output_buffer(); \
}


#define write_string_delta() { \
  copy_string_delta(symbol_string_ptr, next_symbol_string_ptr, out_char_ptr); \
  if (out_char_ptr >= extra_out_char_ptr) \
    write_output_buffer(); \
}


#define write_single_threaded_output() { \
  if (cap_encoded) { \
    symbol = *symbol_array_ptr; \
    while (symbol != -1) { \
      symbol_string_ptr = symbol_strings + symbol_data[symbol].string_index; \
      next_symbol_string_ptr = symbol_strings + symbol_data[symbol + 1].string_index; \
      if (write_caps_on == 1) \
        *out_char_ptr++ = *symbol_string_ptr++ - 0x20; \
      write_caps_on = symbol_data[symbol].type & 1; \
      *symbol_array_ptr++ = -1; \
      if (symbol_array_ptr == symbol_array_end_ptr) \
        symbol_array_ptr = symbol_array_start_ptr; \
      write_string(); \
      symbol = *symbol_array_ptr; \
    } \
  } \
  else if (delta_gap == 0) { \
    symbol = *symbol_array_ptr; \
    while (symbol != -1) { \
      symbol_string_ptr = symbol_strings + symbol_data[symbol].string_index; \
      next_symbol_string_ptr = symbol_strings + symbol_data[symbol + 1].string_index; \
      *symbol_array_ptr++ = -1; \
      if (symbol_array_ptr == symbol_array_end_ptr) \
        symbol_array_ptr = symbol_array_start_ptr; \
      write_string(); \
      symbol = *symbol_array_ptr; \
    } \
  } \
  else { \
    symbol = *symbol_array_ptr; \
    while (symbol != -1) { \
      symbol_string_ptr = symbol_strings + symbol_data[symbol].string_index; \
      next_symbol_string_ptr = symbol_strings + symbol_data[symbol + 1].string_index; \
      *symbol_array_ptr++ = -1; \
      if (symbol_array_ptr == symbol_array_end_ptr) \
        symbol_array_ptr = symbol_array_start_ptr; \
      write_string_delta(); \
      symbol = *symbol_array_ptr; \
    } \
  } \
}


#define manage_symbol_stream(out_char_ptr) { \
  if ((out_symbol_count & 0x1FFFF) == 0) { \
    if (out_symbol_count == 0x40000) { \
      out_symbol_count = 0; \
      if (out_symbol_array[0x20000] != -1) { \
        if (num_threads == 2) \
          while (out_symbol_array[0x20000] != -1); \
        else \
          write_single_threaded_output(); \
      } \
    } \
    else { \
      if (out_symbol_array[0] != -1) { \
        if (num_threads == 2) \
          while (out_symbol_array[0] != -1); \
        else \
          write_single_threaded_output(); \
      } \
    } \
  } \
} \


#define manage_io() { \
  if ((out_symbol_count & 0x1FFFF) == 0) { \
    if (out_symbol_count == 0x40000) { \
      out_symbol_count = 0; \
      if (out_symbol_array[0x20000] != -1) { \
        if (num_threads == 2) \
          while (out_symbol_array[0x20000] != -1); \
        else \
          write_single_threaded_output(); \
      } \
    } \
    else if (out_symbol_array[0] != -1) { \
      if (num_threads == 2) \
        while (out_symbol_array[0] != -1); \
      else \
        write_single_threaded_output(); \
    } \
  } \
}


void *write_output_thread(void *arg) {
  unsigned char *symbol_string_ptr, *next_symbol_string_ptr, *out_char_ptr;
  unsigned char *filename;
  unsigned char write_caps_on;
  unsigned int symbol, *symbol_array_start_ptr, *symbol_array_end_ptr, *symbol_array_ptr;
  volatile unsigned int *vol_symbol_array_ptr;
  volatile struct sym_data *symbol_data_array = symbol_data;
  volatile unsigned char *cap_encoded_ptr = &cap_encoded;

  filename = (unsigned char *)arg;
  if ((fd_out = fopen((char *)arg,"wb")) == NULL) {
    printf("fopen error - fd_out\n");
    exit(0);
  }
  symbol_array_start_ptr = (unsigned int *)out_symbol_array;
  symbol_array_ptr = symbol_array_start_ptr;
  vol_symbol_array_ptr = symbol_array_start_ptr;
  symbol_array_end_ptr = symbol_array_start_ptr + 0x20000;
  while (symbol_array_ptr != symbol_array_end_ptr)
    *symbol_array_ptr++ = -1;
  output_ready = 1;
  symbol_array_end_ptr = symbol_array_start_ptr + 0x40000;
  while (symbol_array_ptr != symbol_array_end_ptr)
    *symbol_array_ptr++ = -1;
  write_caps_on = 0;
  out_buffer_num = 0;
  out_char_ptr = out_char0 + 4;
  start_char_ptr = out_char_ptr;
  extra_out_char_ptr = out_char_ptr + CHARS_TO_WRITE;
  while ((*vol_symbol_array_ptr == -1) && (done_parsing == 0));

  if (*cap_encoded_ptr) {
    while ((done_parsing == 0) || (*vol_symbol_array_ptr != -1)) {
      symbol = *vol_symbol_array_ptr;
      while (symbol != -1) {
        symbol_string_ptr = symbol_strings + symbol_data[symbol].string_index;
        next_symbol_string_ptr = symbol_strings + symbol_data[symbol + 1].string_index;
        if (write_caps_on == 1)
          *out_char_ptr++ = *symbol_string_ptr++ - 0x20;
        write_caps_on = symbol_data_array[symbol].type & 1;
        *vol_symbol_array_ptr++ = -1;
        if (vol_symbol_array_ptr == symbol_array_end_ptr)
          vol_symbol_array_ptr = symbol_array_start_ptr;
        write_string();
        symbol = *vol_symbol_array_ptr;
      }
    }
  }
  else if (delta_gap == 0) {
    while ((done_parsing == 0) || (*vol_symbol_array_ptr != -1)) {
      symbol = *vol_symbol_array_ptr;
      while (symbol != -1) {
        symbol_string_ptr = symbol_strings + symbol_data[symbol].string_index;
        next_symbol_string_ptr = symbol_strings + symbol_data[symbol + 1].string_index;
        *vol_symbol_array_ptr++ = -1;
        if (vol_symbol_array_ptr == symbol_array_end_ptr)
          vol_symbol_array_ptr = symbol_array_start_ptr;
        write_string();
        symbol = *vol_symbol_array_ptr;
      }
    }
  }
  else {
    while ((done_parsing == 0) || (*vol_symbol_array_ptr != -1)) {
      symbol = *vol_symbol_array_ptr;
      while (symbol != -1) {
        symbol_string_ptr = symbol_strings + symbol_data[symbol].string_index;
        next_symbol_string_ptr = symbol_strings + symbol_data[symbol + 1].string_index;
        *vol_symbol_array_ptr++ = -1;
        if (vol_symbol_array_ptr == symbol_array_end_ptr)
          vol_symbol_array_ptr = symbol_array_start_ptr;
        write_string_delta();
        symbol = *vol_symbol_array_ptr;
      }
    }
  }
  chars_to_write = out_char_ptr - start_char_ptr;
  fwrite(start_char_ptr,1,chars_to_write,fd_out);
  fclose(fd_out);
  fprintf(stderr,"Decompressed %u bytes",out_chars+chars_to_write);
}


#define send_symbol() { \
  out_symbol_array[out_symbol_count++] = symbol_number; \
  manage_io(); \
  prior_end = symbol_data[symbol_number].ends; \
}


#define send_symbol_cap() { \
  prior_is_cap = symbol_data[symbol_number].type & 1; \
  send_symbol(); \
}


int main(int argc, char* argv[]) {
  unsigned int *define_symbol_end_ptr;
  unsigned char arg_num, num_inst_codes;
  unsigned long long int start_time;
  pthread_t output_thread;

  start_time = clock();
  arg_num = 1;
  num_threads = 2;
  if (*argv[1] ==  '-') {
    num_threads = *(argv[1]+2) - '0';
    if ((*(argv[1]+1) != 't') || ((num_threads != 1) && (num_threads != 2))) {
      fprintf(stderr,"ERROR - Invalid '-' format.  Only -t1 or -t2 (default) allowed\n");
      exit(0);
    }
    arg_num = 2;
  }

  out_buffers_sent = 0;
  if (num_threads == 2) {
    done_parsing = 0;
    output_ready = 0;
    pthread_create(&output_thread,NULL,write_output_thread,argv[arg_num + 1]);
  }
  else {
    if ((fd_out = fopen(argv[arg_num + 1],"wb")) == NULL) {
      printf("fopen error - unable to create file '%s'\n",argv[arg_num + 1]);
      exit(0);
    }
    symbol_array_start_ptr = (unsigned int *)out_symbol_array;
    symbol_array_ptr = symbol_array_start_ptr;
    symbol_array_end_ptr = symbol_array_start_ptr + 0x40000;
    while (symbol_array_ptr != symbol_array_end_ptr)
      *symbol_array_ptr++ = -1;
    symbol_array_ptr = symbol_array_start_ptr;
    write_caps_on = 0;
    out_buffer_num = 0;
    out_char_ptr = out_char0 + 4;
    start_char_ptr = out_char_ptr;
    extra_out_char_ptr = out_char_ptr + CHARS_TO_WRITE;
  }
  out_chars = 0;

  for (i1 = 2 ; i1 <= MAX_INSTANCES_FOR_MTF_QUEUE ; i1++) {
    mtf_queue_size[i1] = 0;
    mtf_queue_offset[i1] = 0;
  }
  mtfg_queue_0_offset = 0;
  mtfg_queue_8_offset = 0;
  mtfg_queue_16_offset = 0;
  mtfg_queue_32_offset = 0;
  mtfg_queue_64_offset = 0;
  mtfg_queue_128_offset = 0;
  mtfg_queue_192_offset = 0;
  symbol_data[0].string_index = 0;
  num_symbols_defined = 0;
  out_symbol_count = 0;

  if ((fd_in = fopen(argv[arg_num],"rb")) == NULL) {
    printf("fopen error file '%s' not found\n",argv[arg_num]);
    exit(0);
  }
  if (fread(out_char0,1,5,fd_in) != 5) {
    printf("Error - bad input file\n");
    exit(0);
  }

  cap_encoded = out_char0[0] >> 7;
  UTF8_compliant = (out_char0[0] >> 6) & 1;
  use_mtf = (out_char0[0] >> 5) & 1;
  base_bits = out_char0[0] & 0x1F;
  max_code_length = (out_char0[1] & 0x1F) + 1;
  max_regular_code_length = (out_char0[2] & 0x1F) + 1;
  delta_gap = out_char0[1] >> 5;
  if (delta_gap == 3)
    delta_gap = 4;
  mtf_queue_miss_code_length[2] = max_code_length;
  mtf_queue_miss_code_length[3] = mtf_queue_miss_code_length[2] - (out_char0[2] >> 7);
  mtf_queue_miss_code_length[4] = mtf_queue_miss_code_length[3] - ((out_char0[2] >> 6) & 1);
  i1 = 7;
  do {
    mtf_queue_miss_code_length[12 - i1] = mtf_queue_miss_code_length[11 - i1] - ((out_char0[3] >> i1) & 1);
  } while (i1--);
  i1 = 2;
  do {
    mtf_queue_miss_code_length[15 - i1] = mtf_queue_miss_code_length[14 - i1] - ((out_char0[4] >> i1) & 1);
  } while (i1--);
  num_inst_codes = MAX_INSTANCES_FOR_MTF_QUEUE + max_regular_code_length - (out_char0[4] >> 3);
  symbol_data[MAX_SYMBOLS_DEFINED - 1].type = 0;
  i1 = 0x1000;
  while (i1--) {
    i2 = 0x100;
    do {
      lookup_bits[i2][i1] = max_code_length;
    } while (i2--);
  }
  prior_is_cap = 0;

  for (i1 = 0 ; i1 < 8 ; i1++)
    mtfg_queue_0[i1] = MAX_SYMBOLS_DEFINED - 1;
  for (i1 = 0 ; i1 < 8 ; i1++)
    mtfg_queue_8[i1] = MAX_SYMBOLS_DEFINED - 1;
  for (i1 = 0 ; i1 < 16 ; i1++)
    mtfg_queue_16[i1] = MAX_SYMBOLS_DEFINED - 1;
  for (i1 = 0 ; i1 < 32 ; i1++)
    mtfg_queue_32[i1] = MAX_SYMBOLS_DEFINED - 1;
  for (i1 = 0 ; i1 < 64 ; i1++) {
    mtfg_queue_64[i1] = MAX_SYMBOLS_DEFINED - 1;
    mtfg_queue_128[i1] = MAX_SYMBOLS_DEFINED - 1;
    mtfg_queue_192[i1] = MAX_SYMBOLS_DEFINED - 1;
  }

  InitDecoder(fd_in, num_inst_codes);

  i1 = 0xFF;
  if (UTF8_compliant)
    i1 = 0x80;
  do {
    for (i2 = 1 ; i2 <= max_code_length ; i2++) {
      sym_list_ptrs[i1][i2] = (unsigned int *)malloc(sizeof(unsigned int) * INITIAL_LIST_SIZE);
      nsob[i1][i2] = 0;
      nbob[i1][i2] = 0;
      fbob[i1][i2] = 0;
    }
    big_sym_list[i1] = 0;
    bin_bits_under_max[i1] = max_code_length;
    sum_nbob[i1] = 0;
  } while (i1--);
  find_first_symbol = 1;

  if (num_threads == 2)
    while (output_ready == 0);

  // symbol processing loop
  if (cap_encoded) {
    while (1) {
      if (prior_is_cap == 0) {
        DecodeSymTypeStart(LEVEL0);
        if (DecodeSymTypeCheckType0(LEVEL0)) { // dictionary symbol
          DecodeSymTypeFinishType0(LEVEL0);
          if (symbol_data[symbol_number].type & 0x20) {
            if (symbol_data[symbol_number].type & 0x80) {
              DecodeFirstChar(2, prior_end);
            }
            else if (symbol_data[symbol_number].type & 0x40) {
              DecodeFirstChar(3, prior_end);
            }
            else {
              DecodeFirstChar(1, prior_end);
            }
          }
          else {
            DecodeFirstChar(0, prior_end);
          }
          DictionaryBins = sum_nbob[FirstChar];
          DecodeDictionaryBin(lookup_bits[FirstChar]);
          if (CodeLength > bin_bits_under_max[FirstChar]) {
            get_long_symbol();
          }
          else {
            get_short_symbol();
            if ((CodeLength == max_code_length) && (FirstChar == end_symbol) && (BinNum == fbob[FirstChar][max_code_length]))
              break; // EOF
          }
          send_symbol_cap();
          if (symbol_data[symbol_number].instances <= MAX_INSTANCES_FOR_MTF_QUEUE) {
            if (use_mtf) {
              insert_mtf_queue(NOT_CAP);
            }
            else if (--symbol_data[symbol_number].remaining == 0) {
              remove_dictionary_symbol(symbol_number,CodeLength);
            }
          }
          else if (symbol_data[symbol_number].type & 4) {
            add_new_symbol_to_mtfg_queue(symbol_number);
          }
        }
        else if (DecodeSymTypeCheckType1(LEVEL0)) {
          DecodeSymTypeFinishType1(LEVEL0);
          decode_define_cap_encoded(new_symbol_string,0);
          out_symbol_array[out_symbol_count++] = num_symbols_defined - 1;
          manage_symbol_stream(out_char_ptr);
        }
        else if (DecodeSymTypeCheckType2(LEVEL0)) {
          DecodeSymTypeFinishType2(LEVEL0);
          get_mtfg_symbol();
          send_symbol_cap();
        }
        else {
          DecodeSymTypeFinishType3(LEVEL0);
          get_mtf_symbol();
          send_symbol_cap();
        }
      }
      else { // prior_is_cap
        DecodeSymTypeStart(LEVEL0_CAP);
        if (DecodeSymTypeCheckType0(LEVEL0_CAP)) { // dictionary symbol
          DecodeSymTypeFinishType0(LEVEL0_CAP);
          if (symbol_data[symbol_number].type & 0x20) {
            if (symbol_data[symbol_number].type & 0x80) {
              DecodeFirstChar(2, prior_end);
            }
            else if (symbol_data[symbol_number].type & 0x40) {
              DecodeFirstChar(3, prior_end);
            }
            else {
              DecodeFirstChar(1, prior_end);
            }
          }
          else {
            DecodeFirstChar(0, prior_end);
          }
          DictionaryBins = sum_nbob[FirstChar];
          DecodeDictionaryBin(lookup_bits[FirstChar]);
          if (CodeLength > bin_bits_under_max[FirstChar]) {
            get_long_symbol();
          }
          else {
            get_short_symbol();
            if ((CodeLength == max_code_length) && (FirstChar == end_symbol) && (BinNum == fbob[FirstChar][max_code_length]))
              break; // EOF
          }
          send_symbol_cap();
          if (symbol_data[symbol_number].instances <= MAX_INSTANCES_FOR_MTF_QUEUE) {
            if (use_mtf) {
              insert_mtf_queue(CAP);
            }
            else if (--symbol_data[symbol_number].remaining == 0) {
              remove_dictionary_symbol(symbol_number,CodeLength);
            }
          }
          else if ((CodeLength > 10) && (symbol_data[symbol_number].type & 4)) {
            add_new_symbol_to_mtfg_queue(symbol_number);
          }
        }
        else if (DecodeSymTypeCheckType1(LEVEL0_CAP)) {
          DecodeSymTypeFinishType1(LEVEL0_CAP);
          decode_define_cap_encoded(new_symbol_string,0);
          out_symbol_array[out_symbol_count++] = num_symbols_defined - 1;
          manage_symbol_stream(out_char_ptr);
        }
        else if (DecodeSymTypeCheckType2(LEVEL0_CAP)) {
          DecodeSymTypeFinishType2(LEVEL0_CAP);
          get_mtfg_symbol_cap();
          send_symbol_cap();
        }
        else {
          DecodeSymTypeFinishType3(LEVEL0_CAP);
          get_mtf_symbol_cap();
          send_symbol_cap();
        }
      }
    }
  }
  else { // not cap encoded
    while (1) {
      DecodeSymTypeStart(LEVEL0);
      if (DecodeSymTypeCheckType0(LEVEL0)) { // dictionary symbol
        DecodeSymTypeFinishType0(LEVEL0);
        if (UTF8_compliant) {
          DecodeFirstChar(0, prior_end);
        }
        else {
          DecodeFirstCharBinary(prior_end);
        }
        DictionaryBins = sum_nbob[FirstChar];
        DecodeDictionaryBin(lookup_bits[FirstChar]);
        if (CodeLength > bin_bits_under_max[FirstChar]) {
          get_long_symbol();
        }
        else {
          get_short_symbol();
          if ((CodeLength == max_code_length) && (FirstChar == end_symbol) && (BinNum == fbob[FirstChar][max_code_length]))
            break; // EOF
        }
        send_symbol();
        if (symbol_data[symbol_number].instances <= MAX_INSTANCES_FOR_MTF_QUEUE) {
          if (use_mtf) {
            insert_mtf_queue(NOT_CAP);
          }
          else if (--symbol_data[symbol_number].remaining == 0) {
            remove_dictionary_symbol(symbol_number,CodeLength);
          }
        }
        else if (symbol_data[symbol_number].type) {
          add_new_symbol_to_mtfg_queue(symbol_number);
        }
      }
      else if (DecodeSymTypeCheckType1(LEVEL0)) {
        DecodeSymTypeFinishType1(LEVEL0);
        decode_define(new_symbol_string);
        out_symbol_array[out_symbol_count++] = num_symbols_defined - 1;
        manage_symbol_stream(out_char_ptr);
      }
      else if (DecodeSymTypeCheckType2(LEVEL0)) {
        DecodeSymTypeFinishType2(LEVEL0);
        get_mtfg_symbol();
        send_symbol();
      }
      else {
        DecodeSymTypeFinishType3(LEVEL0);
        get_mtf_symbol();
        send_symbol();
      }
    }
  }

  i1 = 0xFF;
  if (UTF8_compliant)
    i1 = 0x80;
  do {
    for (i2 = 1 ; i2 <= max_code_length ; i2++)
      free(sym_list_ptrs[i1][i2]);
  } while (i1--);

  if (num_threads == 2) {
    done_parsing = 1;
    fclose(fd_in);
    pthread_join(output_thread,NULL);
  }
  else {
    fclose(fd_in);
    write_single_threaded_output();
    chars_to_write = out_char_ptr - start_char_ptr;
    fwrite(start_char_ptr,1,chars_to_write,fd_out);
    fclose(fd_out);
    fprintf(stderr,"Decompressed %u bytes",out_chars+chars_to_write);
  }
  fprintf(stderr," in %llu msec\n",clock()-start_time);
}