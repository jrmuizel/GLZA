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

const unsigned char CAP_CHAR = 0x43;
const unsigned int START_UTF8_2BYTE_symbols = 0x80;
const unsigned int START_UTF8_3BYTE_symbols = 0x800;
const unsigned int START_UTF8_4BYTE_symbols = 0x10000;

const unsigned int MAX_INSTANCES_FOR_MTF_QUEUE = 20;
const unsigned int MTF_QUEUE_SIZE = 64;
const unsigned int CHARS_TO_WRITE = 1000000;

unsigned char out_char0[12000000], out_char1[12000000];
unsigned char mtf_queue_miss_code_length[21], mtf_queue_offset[21];
unsigned char symbol_strings[300000000], new_symbol_string[10000000];
unsigned char symbols_remaining[10000000], symbol_instances[10000000];
unsigned char symbol_type[10000000];  // bit 0: string ends CAP_CHAR, bit1: string starts a-z, bit2: nonergodic
unsigned char lookup_bits[0x1000], lookup_bits_cap[0x1000];
unsigned char symbol_count, num_threads, max_code_length, max_regular_code_length;
unsigned char UTF8_compliant, base_bits, cap_encoded, use_mtf, caps_on, prior_is_cap, write_caps_on;
unsigned char out_char_buffer, *start_char_ptr, *extra_out_char_ptr;
unsigned char *symbol_string_ptr, *next_string_ptr, *next_symbol_string_ptr, *out_char_ptr;

unsigned int num_symbols_of_bits[26], num_symbols_of_bits_cap[26];
unsigned int first_bin_of_bits[26], first_bin_of_bits_cap[26];
unsigned int num_bins_of_bits[26], num_bins_of_bits_cap[26];
unsigned int symbol_array_of_bits[26][6000000], symbol_array_of_bits_cap[26][1000000];
unsigned int symbol_array_index[0x00A00000], symbol_array_index_cap[0x00A00000], symbol_string_indexes[0x00A00000];
unsigned int i1, num_symbols_defined, symbol, symbol_number, out_symbol_count;
unsigned int out_chars, out_buffers_sent, chars_to_write, num_az, symbol_index, symbol_to_move;
unsigned int max_symbols_in_max_code_length_bins, max_symbols_in_max_code_length_bins_cap;
unsigned int max_code_length_symbols_per_bin, min_extra_reduce_index;
unsigned int start_mtf_codes, start_mtf_codes_cap;
unsigned int mtf_queue[21][64], mtf_queue_size[21];
unsigned int mtfg_queue_0[8], mtfg_queue_0_offset;
unsigned int mtfg_queue_8[8], mtfg_queue_8_offset;
unsigned int mtfg_queue_16[0x10], mtfg_queue_16_offset;
unsigned int mtfg_queue_32[0x20], mtfg_queue_32_offset;
unsigned int mtfg_queue_64[0x40], mtfg_queue_64_offset;
unsigned int mtfg_queue_128[0x40], mtfg_queue_128_offset;
unsigned int mtfg_queue_192[0x40], mtfg_queue_192_offset;
unsigned int *mtf_queue_ptr, *mtf_queue_last_ptr;
unsigned int *symbol_array_start_ptr, *symbol_array_end_ptr, *symbol_array_ptr;

volatile unsigned char output_ready, done_parsing;
volatile unsigned int out_symbol_array[0x40000];

FILE *fd_in, *fd_out;

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
  *(mtfg_queue_192 + mtfg_queue_192_offset) = 9999999; \
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
  *(mtfg_queue_192 + mtfg_queue_192_offset) = 9999999; \
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
  *(mtfg_queue_192 + mtfg_queue_192_offset) = 9999999; \
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F; \
}


#define remove_mtfg_queue_symbol_128() { \
  while (mtfg_queue_position != 191) { \
    *(mtfg_queue_128 + ((mtfg_queue_128_offset + mtfg_queue_position) & 0x3F)) \
        = *(mtfg_queue_128 + ((mtfg_queue_128_offset + mtfg_queue_position + 1) & 0x3F)); \
    mtfg_queue_position++; \
  } \
  *(mtfg_queue_128 + ((mtfg_queue_128_offset - 1) & 0x3F)) = *(mtfg_queue_192 + mtfg_queue_192_offset); \
  *(mtfg_queue_192 + mtfg_queue_192_offset) = 9999999; \
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F; \
}


#define remove_mtfg_queue_symbol_192() { \
  while (mtfg_queue_position != 255) { \
    *(mtfg_queue_192 + ((mtfg_queue_192_offset + mtfg_queue_position) & 0x3F)) \
        = *(mtfg_queue_192 + ((mtfg_queue_192_offset + mtfg_queue_position + 1) & 0x3F)); \
    mtfg_queue_position++; \
  } \
  *(mtfg_queue_192 + ((mtfg_queue_192_offset + 255) & 0x3F)) = 9999999; \
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
  symbol_type[symbol_number] |= 8; \
  mtfg_queue_8_offset = (mtfg_queue_8_offset - 1) & 7; \
  unsigned int mtfg_queue_symbol_15 = *(mtfg_queue_8 + mtfg_queue_8_offset); \
  mtfg_queue_0_offset = (mtfg_queue_0_offset - 1) & 7; \
  *(mtfg_queue_8 + mtfg_queue_8_offset) = *(mtfg_queue_0 + mtfg_queue_0_offset); \
  *(mtfg_queue_0 + mtfg_queue_0_offset) = symbol_number; \
  if (symbol_instances[mtfg_queue_symbol_15] > 32) { \
    mtfg_queue_16_offset = (mtfg_queue_16_offset - 1) & 0xF; \
    unsigned int mtfg_queue_symbol_31 = *(mtfg_queue_16 + mtfg_queue_16_offset); \
    *(mtfg_queue_16 + mtfg_queue_16_offset) = mtfg_queue_symbol_15; \
    if (symbol_instances[mtfg_queue_symbol_31] != 33) { \
      mtfg_queue_32_offset = (mtfg_queue_32_offset - 1) & 0x1F; \
      unsigned int mtfg_queue_symbol_63 = *(mtfg_queue_32 + mtfg_queue_32_offset); \
      *(mtfg_queue_32 + mtfg_queue_32_offset) = mtfg_queue_symbol_31; \
      if (symbol_instances[mtfg_queue_symbol_63] != 34) { \
        mtfg_queue_64_offset = (mtfg_queue_64_offset - 1) & 0x3F; \
        unsigned int mtfg_queue_symbol_127 = *(mtfg_queue_64 + mtfg_queue_64_offset); \
        *(mtfg_queue_64 + mtfg_queue_64_offset) = mtfg_queue_symbol_63; \
        if (symbol_instances[mtfg_queue_symbol_127] != 35) { \
          mtfg_queue_128_offset = (mtfg_queue_128_offset - 1) & 0x3F; \
          unsigned int mtfg_queue_symbol_191 = *(mtfg_queue_128 + mtfg_queue_128_offset); \
          *(mtfg_queue_128 + mtfg_queue_128_offset) = mtfg_queue_symbol_127; \
          if (symbol_instances[mtfg_queue_symbol_191] != 36) { \
            mtfg_queue_192_offset = (mtfg_queue_192_offset - 1) & 0x3F; \
            symbol_type[*(mtfg_queue_192 + mtfg_queue_192_offset)] &= 7; \
            *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191; \
          } \
          else \
            symbol_type[mtfg_queue_symbol_191] &= 7; \
        } \
        else \
          symbol_type[mtfg_queue_symbol_127] &= 7; \
      } \
      else \
        symbol_type[mtfg_queue_symbol_63] &= 7; \
    } \
    else \
      symbol_type[mtfg_queue_symbol_31] &= 7; \
  } \
  else \
    symbol_type[mtfg_queue_symbol_15] &= 7; \
}


#define update_mtfg_queue() { \
  unsigned int mtfg_queue_symbol_15, mtfg_queue_symbol_31, mtfg_queue_symbol_63, mtfg_queue_symbol_127, mtfg_queue_symbol_191; \
  if (mtfg_queue_position < 8) { \
    if (mtfg_queue_position < 5) { \
      mtfg_queue_position += mtfg_queue_0_offset; \
      symbol_number = mtfg_queue_0[mtfg_queue_position & 7]; \
      while (mtfg_queue_position != mtfg_queue_0_offset) { \
        *(mtfg_queue_0 + (mtfg_queue_position & 7)) = *(mtfg_queue_0 + ((mtfg_queue_position - 1) & 7)); \
        mtfg_queue_position--; \
      } \
    } \
    else { \
      mtfg_queue_position += mtfg_queue_0_offset; \
      symbol_number = mtfg_queue_0[mtfg_queue_position & 7]; \
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
      mtfg_queue_position += mtfg_queue_8_offset - 8; \
      symbol_number = *(mtfg_queue_8 + (mtfg_queue_position & 7)); \
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
      if (symbol_instances[mtfg_queue_symbol_15] <= 32) { \
        symbol_type[mtfg_queue_symbol_15] &= 7; \
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
    if (symbol_instances[mtfg_queue_symbol_15] <= 32) { \
      symbol_type[mtfg_queue_symbol_15] &= 7; \
      remove_mtfg_queue_symbol_32(); \
    } \
    else { \
      increment_mtfg_queue_16(); \
      if (symbol_instances[mtfg_queue_symbol_31] == 33) { \
        symbol_type[mtfg_queue_symbol_31] &= 7; \
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
    if (symbol_instances[mtfg_queue_symbol_15] <= 32) { \
      symbol_type[mtfg_queue_symbol_15] &= 7; \
      remove_mtfg_queue_symbol_64(); \
    } \
    else { \
      increment_mtfg_queue_16(); \
      if (symbol_instances[mtfg_queue_symbol_31] == 33) { \
        symbol_type[mtfg_queue_symbol_31] &= 7; \
        remove_mtfg_queue_symbol_64(); \
      } \
      else { \
        increment_mtfg_queue_32(); \
        if (symbol_instances[mtfg_queue_symbol_63] == 34) { \
          symbol_type[mtfg_queue_symbol_63] &= 7; \
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
    if (symbol_instances[mtfg_queue_symbol_15] <= 32) { \
      symbol_type[mtfg_queue_symbol_15] &= 7; \
      remove_mtfg_queue_symbol_128(); \
    } \
    else { \
      increment_mtfg_queue_16(); \
      if (symbol_instances[mtfg_queue_symbol_31] == 33) { \
        symbol_type[mtfg_queue_symbol_31] &= 7; \
        remove_mtfg_queue_symbol_128(); \
      } \
      else { \
        increment_mtfg_queue_32(); \
        if (symbol_instances[mtfg_queue_symbol_63] == 34) { \
          symbol_type[mtfg_queue_symbol_63] &= 7; \
          remove_mtfg_queue_symbol_128(); \
        } \
        else { \
          increment_mtfg_queue_64(); \
          if (symbol_instances[mtfg_queue_symbol_127] == 35) { \
            symbol_type[mtfg_queue_symbol_127] &= 7; \
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
    if (symbol_instances[mtfg_queue_symbol_15] <= 32) { \
      symbol_type[mtfg_queue_symbol_15] &= 7; \
      remove_mtfg_queue_symbol_192(); \
    } \
    else { \
      increment_mtfg_queue_16(); \
      if (symbol_instances[mtfg_queue_symbol_31] == 33) { \
        symbol_type[mtfg_queue_symbol_31] &= 7; \
        remove_mtfg_queue_symbol_192(); \
      } \
      else { \
        increment_mtfg_queue_32(); \
        if (symbol_instances[mtfg_queue_symbol_63] == 34) { \
          symbol_type[mtfg_queue_symbol_63] &= 7; \
          remove_mtfg_queue_symbol_192(); \
        } \
        else { \
          increment_mtfg_queue_64(); \
          if (symbol_instances[mtfg_queue_symbol_127] == 35) { \
            symbol_type[mtfg_queue_symbol_127] &= 7; \
            remove_mtfg_queue_symbol_192(); \
          } \
          else { \
            increment_mtfg_queue_128(); \
            if (symbol_instances[mtfg_queue_symbol_191] == 36) { \
              symbol_type[mtfg_queue_symbol_191] &= 7; \
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
  symbol_type[symbol_number] |= 8; \
}


#define get_mtfg_symbol() { \
  DecodeMtfgQueuePos(NOT_CAP); \
  update_mtfg_queue(); \
}


#define get_mtfg_symbol_cap() { \
  DecodeMtfgQueuePos(CAP); \
  unsigned int find_caps = mtfg_queue_position + 1; \
  unsigned int cap_queue_position = mtfg_queue_0_offset; \
  do { \
    if (symbol_type[*(mtfg_queue_0 + (cap_queue_position & 7))] & 2) { \
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
      if (symbol_type[*(mtfg_queue_8 + (cap_queue_position & 7))] & 2) { \
        find_caps--; \
        if (find_caps == 0) \
          break; \
      } \
      else \
        mtfg_queue_position++; \
      cap_queue_position = (cap_queue_position + 1) & 7; \
    } while (cap_queue_position != mtfg_queue_8_offset); \
  }\
  if (find_caps) { \
    cap_queue_position = mtfg_queue_16_offset; \
    do { \
      if (symbol_type[*(mtfg_queue_16 + (cap_queue_position & 0xF))] & 2) { \
        find_caps--; \
        if (find_caps == 0) \
          break; \
      } \
      else \
        mtfg_queue_position++; \
      cap_queue_position = (cap_queue_position + 1) & 0xF; \
    } while (cap_queue_position != mtfg_queue_16_offset); \
  }\
  if (find_caps) { \
    cap_queue_position = mtfg_queue_32_offset; \
    do { \
      if (symbol_type[*(mtfg_queue_32 + (cap_queue_position & 0x1F))] & 2) { \
        find_caps--; \
        if (find_caps == 0) \
          break; \
      } \
      else \
        mtfg_queue_position++; \
      cap_queue_position = (cap_queue_position + 1) & 0x1F; \
    } while (cap_queue_position != mtfg_queue_32_offset); \
  }\
  if (find_caps) { \
    cap_queue_position = mtfg_queue_64_offset; \
    do { \
      if (symbol_type[*(mtfg_queue_64 + (cap_queue_position & 0x3F))] & 2) { \
        find_caps--; \
        if (find_caps == 0) \
          break; \
      } \
      else \
        mtfg_queue_position++; \
      cap_queue_position = (cap_queue_position + 1) & 0x3F; \
    } while (cap_queue_position != mtfg_queue_64_offset); \
  }\
  if (find_caps) { \
    cap_queue_position = mtfg_queue_128_offset; \
    do { \
      if (symbol_type[*(mtfg_queue_128 + (cap_queue_position & 0x3F))] & 2) { \
        find_caps--; \
        if (find_caps == 0) \
          break; \
      } \
      else \
        mtfg_queue_position++; \
      cap_queue_position = (cap_queue_position + 1) & 0x3F; \
    } while (cap_queue_position != mtfg_queue_128_offset); \
  }\
  if (find_caps) { \
    cap_queue_position = mtfg_queue_192_offset; \
    do { \
      if (symbol_type[*(mtfg_queue_192 + (cap_queue_position & 0x3F))] & 2) { \
        find_caps--; \
        if (find_caps == 0) \
          break; \
      } \
      else \
        mtfg_queue_position++; \
      cap_queue_position = (cap_queue_position + 1) & 0x3F; \
    } while (cap_queue_position != mtfg_queue_192_offset); \
  }\
  update_mtfg_queue(); \
}


inline void update_code_length_tables(unsigned char code_length) {
  if (code_length >= 12) {
    if (symbol_index >= (num_bins_of_bits[code_length] << (code_length - 12))) {
      start_mtf_codes++;
      if (code_length == max_code_length) {
        num_bins_of_bits[max_code_length]++;
        max_symbols_in_max_code_length_bins += max_code_length_symbols_per_bin;
      }
      else {
        unsigned char bits = code_length;
        lookup_bits[first_bin_of_bits[bits] + num_bins_of_bits[bits]++] = bits;
        while (++bits != max_code_length) {
          if (num_bins_of_bits[bits])
            lookup_bits[first_bin_of_bits[bits] + num_bins_of_bits[bits]] = bits;
          first_bin_of_bits[bits]++;
        }
        first_bin_of_bits[bits]++;
      }
    }
  }
  else {
    if ((symbol_index << (12 - code_length)) == num_bins_of_bits[code_length]) {
      start_mtf_codes += 1 << (12 - code_length);
      if (code_length == max_code_length) {
        num_bins_of_bits[max_code_length] += 1 << (12 - code_length);
        max_symbols_in_max_code_length_bins++;
      }
      else {
        do {
          unsigned char bits = code_length;
          lookup_bits[first_bin_of_bits[bits] + num_bins_of_bits[bits]++] = bits;
          while (++bits != max_code_length) {
            if (num_bins_of_bits[bits])
              lookup_bits[first_bin_of_bits[bits] + num_bins_of_bits[bits]] = bits;
            first_bin_of_bits[bits]++;
          }
        } while (((symbol_index + 1) << (12 - code_length)) != num_bins_of_bits[code_length]);
        first_bin_of_bits[max_code_length] += 1 << (12 - code_length);
      }
    }
  }
}


inline void update_code_length_tables_cap(unsigned char code_length, unsigned int symbol_number) {
  symbol_index = num_symbols_of_bits_cap[code_length]++;
  symbol_array_of_bits_cap[code_length][symbol_index] = symbol_number;
  symbol_array_index_cap[symbol_number] = symbol_index;
  if (code_length >= 12) {
    if (symbol_index >= (num_bins_of_bits_cap[code_length] << (code_length - 12))) {
      start_mtf_codes_cap++;
      if (code_length == max_code_length) {
        num_bins_of_bits_cap[max_code_length]++;
        max_symbols_in_max_code_length_bins_cap += max_code_length_symbols_per_bin;
      }
      else {
        unsigned char bits = code_length;
        lookup_bits_cap[first_bin_of_bits_cap[bits] + num_bins_of_bits_cap[bits]++] = bits;
        while (++bits != max_code_length) {
          if (num_bins_of_bits_cap[bits])
            lookup_bits_cap[first_bin_of_bits_cap[bits] + num_bins_of_bits_cap[bits]] = bits;
          first_bin_of_bits_cap[bits]++;
        }
        first_bin_of_bits_cap[bits]++;
      }
    }
  }
  else {
    if ((symbol_index << (12 - code_length)) == num_bins_of_bits_cap[code_length]) {
      start_mtf_codes_cap += 1 << (12 - code_length);
      if (code_length == max_code_length) {
        num_bins_of_bits_cap[max_code_length] += 1 << (12 - code_length);
        max_symbols_in_max_code_length_bins_cap++;
      }
      else {
        do {
          unsigned char bits = code_length;
          lookup_bits_cap[first_bin_of_bits_cap[bits] + num_bins_of_bits_cap[bits]++] = bits;
          while (++bits != max_code_length) {
            if (num_bins_of_bits_cap[bits])
              lookup_bits_cap[first_bin_of_bits_cap[bits] + num_bins_of_bits_cap[bits]] = bits;
            first_bin_of_bits_cap[bits]++;
          }
        } while (((symbol_index + 1) << (12 - code_length)) != num_bins_of_bits_cap[code_length]);
        first_bin_of_bits_cap[max_code_length] += 1 << (12 - code_length);
      }
    }
  }
}


inline void insert_mtf_queue() {
  symbol_index = symbol_array_index[symbol_number];
  symbol_count = symbol_instances[symbol_number];
  if (--symbols_remaining[symbol_number]) { // move the symbol back into the mtf queue
    mtf_queue_number = symbol_count - 2;
    UpFreqMtfQueueNumD(NOT_CAP);
    if (mtf_queue_size[symbol_count] != MTF_QUEUE_SIZE) { // remove symbol from symbol list
      symbol_to_move = symbol_array_of_bits[CodeLength][--num_symbols_of_bits[CodeLength]];
      symbol_array_of_bits[CodeLength][symbol_index] = symbol_to_move;
      symbol_array_index[symbol_to_move] = symbol_index;
      mtf_queue[symbol_count][((mtf_queue_offset[symbol_count] + mtf_queue_size[symbol_count]++) & 0x3F)] = symbol_number;
    }
    else { // swap symbol list symbol with queue symbol
      mtf_queue_ptr = &mtf_queue[symbol_count][mtf_queue_offset[symbol_count]];
      symbol_to_move = *mtf_queue_ptr;
      symbol_array_of_bits[CodeLength][symbol_index] = symbol_to_move;
      symbol_array_index[symbol_to_move] = symbol_index;
      // put symbol in queue and rotate cyclical buffer
      *mtf_queue_ptr = symbol_number;
      mtf_queue_offset[symbol_count] = (mtf_queue_offset[symbol_count] + 1) & 0x3F;
    }
  }
  else { // remove symbol from symbol list
    symbol_to_move = symbol_array_of_bits[CodeLength][--num_symbols_of_bits[CodeLength]];
    symbol_array_of_bits[CodeLength][symbol_index] = symbol_to_move;
    symbol_array_index[symbol_to_move] = symbol_index;
  }
}


inline void insert_mtf_queue_cap_encoded()
{
  symbol_index = symbol_array_index[symbol_number];
  symbol_count = symbol_instances[symbol_number];
  if (--symbols_remaining[symbol_number]) { // move the symbol back into the mtf queue
    mtf_queue_number = symbol_count - 2;
    UpFreqMtfQueueNumD(NOT_CAP);
    if (mtf_queue_size[symbol_count] != MTF_QUEUE_SIZE) {
      mtf_queue[symbol_count][(mtf_queue_offset[symbol_count] + mtf_queue_size[symbol_count]++) & 0x3F] = symbol_number;
      // remove symbol from symbol list
      symbol_to_move = symbol_array_of_bits[CodeLength][--num_symbols_of_bits[CodeLength]];
      symbol_array_of_bits[CodeLength][symbol_index] = symbol_to_move;
      symbol_array_index[symbol_to_move] = symbol_index;
      if (symbol_type[symbol_number] & 2) { // remove symbol from cap symbol list
        symbol_index = symbol_array_index_cap[symbol_number];
        symbol_to_move = symbol_array_of_bits_cap[CodeLength][--num_symbols_of_bits_cap[CodeLength]];
        symbol_array_of_bits_cap[CodeLength][symbol_index] = symbol_to_move;
        symbol_array_index_cap[symbol_to_move] = symbol_index;
      }
    }
    else { // swap symbol list symbol with queue symbol
      mtf_queue_ptr = &mtf_queue[symbol_count][mtf_queue_offset[symbol_count]];
      symbol_to_move = *mtf_queue_ptr;
      symbol_array_of_bits[CodeLength][symbol_index] = symbol_to_move;
      symbol_array_index[symbol_to_move] = symbol_index;
      if (symbol_type[symbol_number] & 2) {
        symbol_index = symbol_array_index_cap[symbol_number];
        if (symbol_type[symbol_to_move] & 2) { // swap cap symbol list symbol with queue symbol
          symbol_array_of_bits_cap[CodeLength][symbol_index] = symbol_to_move;
          symbol_array_index_cap[symbol_to_move] = symbol_index;
        }
        else { // remove symbol from cap symbol list
          symbol_to_move = symbol_array_of_bits_cap[CodeLength][--num_symbols_of_bits_cap[CodeLength]];
          symbol_array_of_bits_cap[CodeLength][symbol_index] = symbol_to_move;
          symbol_array_index_cap[symbol_to_move] = symbol_index;
        }
      }
      else if (symbol_type[symbol_to_move] & 2) { // add symbol to cap symbol list
        update_code_length_tables_cap(CodeLength, symbol_to_move);
      }
      // put symbol in queue and rotate cyclical buffer
      *mtf_queue_ptr = symbol_number;
      mtf_queue_offset[symbol_count] = (mtf_queue_offset[symbol_count] + 1) & 0x3F;
    }
  }
  else { // remove symbol from symbol list
    symbol_to_move = symbol_array_of_bits[CodeLength][--num_symbols_of_bits[CodeLength]];
    symbol_array_of_bits[CodeLength][symbol_index] = symbol_to_move;
    symbol_array_index[symbol_to_move] = symbol_index;
    if (symbol_type[symbol_number] & 2) { // remove symbol from cap symbol list
      symbol_index = symbol_array_index_cap[symbol_number];
      symbol_to_move = symbol_array_of_bits_cap[CodeLength][--num_symbols_of_bits_cap[CodeLength]];
      symbol_array_of_bits_cap[CodeLength][symbol_index] = symbol_to_move;
      symbol_array_index_cap[symbol_to_move] = symbol_index;
    }
  }
}


inline void insert_mtf_queue_cap_encoded_cap() {
  symbol_index = symbol_array_index[symbol_number];
  symbol_count = symbol_instances[symbol_number];
  if (--symbols_remaining[symbol_number]) { // move the symbol back into the mtf queue
    mtf_queue_number = symbol_count - 2;
    UpFreqMtfQueueNumD(CAP);
    if (mtf_queue_size[symbol_count] != MTF_QUEUE_SIZE) { // remove symbol from symbol lists
      mtf_queue[symbol_count][(mtf_queue_offset[symbol_count] + mtf_queue_size[symbol_count]++) & 0x3F] = symbol_number;
      symbol_to_move = symbol_array_of_bits[CodeLength][--num_symbols_of_bits[CodeLength]];
      symbol_array_of_bits[CodeLength][symbol_index] = symbol_to_move;
      symbol_array_index[symbol_to_move] = symbol_index;
      symbol_index = symbol_array_index_cap[symbol_number];
      symbol_to_move = symbol_array_of_bits_cap[CodeLength][--num_symbols_of_bits_cap[CodeLength]];
      symbol_array_of_bits_cap[CodeLength][symbol_index] = symbol_to_move;
      symbol_array_index_cap[symbol_to_move] = symbol_index;
    }
    else { // swap symbol list symbol with queue symbol
      mtf_queue_ptr = &mtf_queue[symbol_count][mtf_queue_offset[symbol_count]];
      symbol_to_move = *mtf_queue_ptr;
      symbol_array_of_bits[CodeLength][symbol_index] = symbol_to_move;
      symbol_array_index[symbol_to_move] = symbol_index;
      symbol_index = symbol_array_index_cap[symbol_number];
      if (symbol_type[symbol_to_move] & 2) { // swap cap table symbols
        symbol_array_of_bits_cap[CodeLength][symbol_index] = symbol_to_move;
        symbol_array_index_cap[symbol_to_move] = symbol_index;
      }
      else { // remove symbol from cap symbol list
        symbol_to_move = symbol_array_of_bits_cap[CodeLength][--num_symbols_of_bits_cap[CodeLength]];
        symbol_array_of_bits_cap[CodeLength][symbol_index] = symbol_to_move;
        symbol_array_index_cap[symbol_to_move] = symbol_index;
      }
      // put symbol in queue and rotate cyclical buffer
      *mtf_queue_ptr = symbol_number;
      mtf_queue_offset[symbol_count] = (mtf_queue_offset[symbol_count] + 1) & 0x3F;
    }
  }
  else { // remove symbol from symbol lists
    symbol_to_move = symbol_array_of_bits[CodeLength][--num_symbols_of_bits[CodeLength]];
    symbol_array_of_bits[CodeLength][symbol_index] = symbol_to_move;
    symbol_array_index[symbol_to_move] = symbol_index;
    symbol_index = symbol_array_index_cap[symbol_number];
    symbol_to_move = symbol_array_of_bits_cap[CodeLength][--num_symbols_of_bits_cap[CodeLength]];
    symbol_array_of_bits_cap[CodeLength][symbol_index] = symbol_to_move;
    symbol_array_index_cap[symbol_to_move] = symbol_index;
  }
}


inline void check_last_symbol() {
  if (--symbols_remaining[symbol_number] == 0) { // remove symbol from symbol list
    symbol_index = symbol_array_index[symbol_number];
    symbol_to_move = symbol_array_of_bits[CodeLength][--num_symbols_of_bits[CodeLength]];
    symbol_array_of_bits[CodeLength][symbol_index = symbol_array_index[symbol_number]] = symbol_to_move;
    symbol_array_index[symbol_to_move] = symbol_index;
  }
}


inline void check_last_symbol_cap_encoded() {
  if (--symbols_remaining[symbol_number] == 0) { // remove symbol from symbol list
    symbol_index = symbol_array_index[symbol_number];
    symbol_to_move = symbol_array_of_bits[CodeLength][--num_symbols_of_bits[CodeLength]];
    symbol_array_of_bits[CodeLength][symbol_index] = symbol_to_move;
    symbol_array_index[symbol_to_move] = symbol_index;
    if (symbol_type[symbol_number] & 2) { // remove symbol from cap symbol list
      symbol_index = symbol_array_index_cap[symbol_number];
      symbol_to_move = symbol_array_of_bits_cap[CodeLength][--num_symbols_of_bits_cap[CodeLength]];
      symbol_array_of_bits_cap[CodeLength][symbol_index] = symbol_to_move;
      symbol_array_index_cap[symbol_to_move] = symbol_index;
    }
  }
}


inline void check_last_symbol_cap_encoded_cap() {
  if (--symbols_remaining[symbol_number] == 0) { // remove symbol from symbol lists
    symbol_index = symbol_array_index[symbol_number];
    symbol_to_move = symbol_array_of_bits[CodeLength][--num_symbols_of_bits[CodeLength]];
    symbol_array_of_bits[CodeLength][symbol_index] = symbol_to_move;
    symbol_array_index[symbol_to_move] = symbol_index;
    symbol_index = symbol_array_index_cap[symbol_number];
    symbol_to_move = symbol_array_of_bits_cap[CodeLength][--num_symbols_of_bits_cap[CodeLength]];
    symbol_array_of_bits_cap[CodeLength][symbol_index] = symbol_to_move;
    symbol_array_index_cap[symbol_to_move] = symbol_index;
  }
}


#define get_long_symbol() \
{ \
  char index_bits = CodeLength - 12; \
  unsigned int msib = num_bins_of_bits[CodeLength] << index_bits; \
  unsigned int reduce_bits = 0; \
  unsigned int shifted_max_symbols = msib >> 1; \
  while (shifted_max_symbols >= num_symbols_of_bits[CodeLength]) { \
    reduce_bits++; \
    shifted_max_symbols >>= 1; \
  } \
  if (index_bits > reduce_bits) { \
    min_extra_reduce_index = (num_symbols_of_bits[CodeLength] << 1) - (msib >> reduce_bits); \
    DecodeDictionarySymbolIndex(index_bits-reduce_bits,first_bin_of_bits[CodeLength],symbol_array_of_bits[CodeLength]); \
    symbol_number = symbol_array_of_bits[CodeLength][SymbolIndex]; \
  } \
  else { \
    SymbolIndex = BinNum - first_bin_of_bits[CodeLength]; \
    if ((SymbolIndex == 0) && (CodeLength == max_code_length)) \
      break; /* EOF */ \
    unsigned int extra_code_bins = 0; \
    int index = SymbolIndex; \
    while ((symbol_type[symbol_array_of_bits[CodeLength][--index]] & 8) && (index >= 0)) \
      extra_code_bins++; \
    low -= range * extra_code_bins; \
    while (symbol_type[symbol_array_of_bits[CodeLength][SymbolIndex]] & 8) { \
      extra_code_bins++; \
      SymbolIndex++; \
    } \
    range *= 1 + extra_code_bins; \
    symbol_number = symbol_array_of_bits[CodeLength][SymbolIndex]; \
  } \
}


#define get_long_symbol_cap() \
{ \
  char index_bits = CodeLength - 12; \
  unsigned int msib = num_bins_of_bits_cap[CodeLength] << index_bits; \
  unsigned int reduce_bits = 0; \
  unsigned int shifted_max_symbols = msib >> 1; \
  while (shifted_max_symbols >= num_symbols_of_bits_cap[CodeLength]) { \
    reduce_bits++; \
    shifted_max_symbols >>= 1; \
  } \
  if (CodeLength - 12 > reduce_bits) { \
    min_extra_reduce_index = (num_symbols_of_bits_cap[CodeLength] << 1) - (msib >> reduce_bits); \
    DecodeDictionarySymbolIndex(index_bits-reduce_bits,first_bin_of_bits_cap[CodeLength],symbol_array_of_bits_cap[CodeLength]); \
    symbol_number = symbol_array_of_bits_cap[CodeLength][SymbolIndex]; \
  } \
  else { \
    SymbolIndex = BinNum - first_bin_of_bits_cap[CodeLength]; \
    if ((SymbolIndex == 0) && (CodeLength == max_code_length)) \
      break; /* EOF */ \
    unsigned int extra_code_bins = 0; \
    int index = SymbolIndex; \
    while ((symbol_type[symbol_array_of_bits_cap[CodeLength][--index]] & 8) && (index >= 0)) \
      extra_code_bins++; \
    low -= range * extra_code_bins; \
    while (symbol_type[symbol_array_of_bits_cap[CodeLength][SymbolIndex]] & 8) \
      extra_code_bins += (++SymbolIndex >= min_extra_reduce_index) ? 2 : 1; \
    range *= 1 + extra_code_bins; \
    symbol_number = symbol_array_of_bits_cap[CodeLength][SymbolIndex]; \
  } \
}


#define get_short_symbol() \
{ \
  unsigned int extra_code_bins = 0; \
  unsigned int index = (BinNum - first_bin_of_bits[CodeLength]) >> (12 - CodeLength); \
  int temp_index = index; \
  while ((--temp_index >= 0) && (symbol_type[symbol_array_of_bits[CodeLength][temp_index]] & 8)) { \
    extra_code_bins++; \
  } \
  low -= range * extra_code_bins; \
  while (symbol_type[symbol_array_of_bits[CodeLength][index]] & 8) { \
    index++; \
    extra_code_bins++; \
  } \
  range *= 1 + extra_code_bins; \
  symbol_number = symbol_array_of_bits[CodeLength][index]; \
}


#define get_short_symbol_cap() \
{ \
  unsigned int extra_code_bins = 0; \
  unsigned int index = (BinNum - first_bin_of_bits_cap[CodeLength]) >> (12 - CodeLength); \
  int temp_index = index; \
  while ((--temp_index >= 0) && (symbol_type[symbol_array_of_bits_cap[CodeLength][temp_index]] & 8)) { \
    extra_code_bins++; \
  } \
  low -= range * extra_code_bins; \
  while (symbol_type[symbol_array_of_bits_cap[CodeLength][index]] & 8) { \
    index++; \
    extra_code_bins++; \
  } \
  range *= 1 + extra_code_bins; \
  symbol_number = symbol_array_of_bits_cap[CodeLength][index]; \
}


void get_mtf_symbol() {
  DecodeMtfQueueNum(NOT_CAP);
  DecodeMtfQueuePos(NOT_CAP);
  if (mtf_queue_number == 0) {
    if (Symbol == 0) { // queue position 0
      symbol_number = mtf_queue[2][(mtf_queue_offset[2] + mtf_queue_size[2] - 1) & 0x3F];
      mtf_queue_size[2]--;
    }
    else {
      unsigned int mtf_queue_last_position = (mtf_queue_offset[2] + --mtf_queue_size[2]) & 0x3F;
      unsigned int mtf_queue_position = (mtf_queue_last_position - Symbol) & 0x3F;
      unsigned int *mtf_queue_ptr = &mtf_queue[2][0];
      symbol_number = *(mtf_queue_ptr + mtf_queue_position);
      do { // move the newer symbols up
        *(mtf_queue_ptr + mtf_queue_position) = *(mtf_queue_ptr + ((mtf_queue_position + 1) & 0x3F));
        mtf_queue_position = (mtf_queue_position + 1) & 0x3F;
      } while (mtf_queue_position != mtf_queue_last_position);
    }
  }
  else {
    mtf_queue_number += 2;
    if (Symbol == 0) { // queue position 0
      symbol_number = mtf_queue[mtf_queue_number]
          [(mtf_queue_offset[mtf_queue_number] + mtf_queue_size[mtf_queue_number] - 1) & 0x3F];
      // decrement the mtf queue size if this is the last instance of this symbol
      if (--symbols_remaining[symbol_number]) {
        mtf_queue_number -= 2;
        UpFreqMtfQueueNumHitD(NOT_CAP);
      }
      else {
        mtf_queue_size[mtf_queue_number]--;
      }
    }
    else {
      unsigned int mtf_queue_last_position
          = (mtf_queue_offset[mtf_queue_number] + mtf_queue_size[mtf_queue_number] - 1) & 0x3F;
      unsigned int mtf_queue_position = (mtf_queue_last_position - Symbol) & 0x3F;
      // remove this symbol from its current mtf queue position
      unsigned int *mtf_queue_ptr = &mtf_queue[mtf_queue_number][0];
      symbol_number = *(mtf_queue_ptr + mtf_queue_position);
      do { // move the newer symbols up
        *(mtf_queue_ptr + mtf_queue_position) = *(mtf_queue_ptr + ((mtf_queue_position + 1) & 0x3F));
        mtf_queue_position = (mtf_queue_position + 1) & 0x3F;
      } while (mtf_queue_position != mtf_queue_last_position);
      if (--symbols_remaining[symbol_number]) { // put symbol on top of mtf queue
        *(mtf_queue_ptr + mtf_queue_position) = symbol_number;
        mtf_queue_number -= 2;
        UpFreqMtfQueueNumHitD(NOT_CAP);
      }
      else { // last instance - decrement the mtf queue size
        mtf_queue_size[mtf_queue_number]--;
      }
    }
  }
}


void get_mtf_symbol_cap() {
  DecodeMtfQueueNum(CAP);
  DecodeMtfQueuePos(CAP);
  if (mtf_queue_number == 0) {
    if (Symbol == 0) { // queue position 0
      num_az = 0;
      mtf_queue_last_ptr = &mtf_queue[2][(mtf_queue_offset[2] + mtf_queue_size[2] - 1) & 0x3F];
      mtf_queue_ptr = mtf_queue_last_ptr;
      while ((symbol_type[*mtf_queue_ptr] & 2) == 0) {
        if (mtf_queue_ptr-- == &mtf_queue[2][0])
          mtf_queue_ptr += MTF_QUEUE_SIZE;
      }
      symbol_number = *mtf_queue_ptr;
      while (mtf_queue_ptr != mtf_queue_last_ptr) { // move the higher symbols down
        if (mtf_queue_ptr < &mtf_queue[2][0] + MTF_QUEUE_SIZE - 1) {
          *mtf_queue_ptr = *(mtf_queue_ptr + 1);
          mtf_queue_ptr++;
        }
        else {
          *mtf_queue_ptr = *(mtf_queue_ptr - MTF_QUEUE_SIZE + 1);
          mtf_queue_ptr -= MTF_QUEUE_SIZE - 1;
        }
      }
      mtf_queue_size[2]--;
    }
    else {
      mtf_queue_last_ptr = &mtf_queue[2][(mtf_queue_offset[2] + mtf_queue_size[2] - 1) & 0x3F];
      // remove this symbol from its current mtf queue position
      num_az = Symbol + 1;
      mtf_queue_ptr = mtf_queue_last_ptr + 1;
      do {
        if (mtf_queue_ptr != &mtf_queue[2][0])
          mtf_queue_ptr--;
        else
          mtf_queue_ptr += MTF_QUEUE_SIZE - 1;
        if (symbol_type[*mtf_queue_ptr] & 2)
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
      } while (mtf_queue_ptr != mtf_queue_last_ptr);
      mtf_queue_size[2]--;
    }
  }
  else {
    mtf_queue_number += 2;
    if (Symbol == 0) { // queue position 0
      num_az = 0;
      mtf_queue_last_ptr = &mtf_queue[mtf_queue_number]
          [(mtf_queue_offset[mtf_queue_number] + mtf_queue_size[mtf_queue_number] - 1) & 0x3F];
      mtf_queue_ptr = mtf_queue_last_ptr;
      while ((symbol_type[*mtf_queue_ptr] & 2) == 0) {
        if (mtf_queue_ptr-- == &mtf_queue[mtf_queue_number][0])
          mtf_queue_ptr += MTF_QUEUE_SIZE;
      }
      symbol_number = *mtf_queue_ptr;
      while (mtf_queue_ptr != mtf_queue_last_ptr) { // move the higher symbols down
        if (mtf_queue_ptr < &mtf_queue[mtf_queue_number][0] + MTF_QUEUE_SIZE - 1) {
          *mtf_queue_ptr = *(mtf_queue_ptr + 1);
          mtf_queue_ptr++;
        }
        else {
          *mtf_queue_ptr = *(mtf_queue_ptr - MTF_QUEUE_SIZE + 1);
          mtf_queue_ptr -= MTF_QUEUE_SIZE - 1;
        }
      }
      if (--symbols_remaining[symbol_number]) { // put symbol on top of mtf queue
        *mtf_queue_ptr = symbol_number;
        mtf_queue_number -= 2;
        UpFreqMtfQueueNumHitD(CAP);
      }
      else { // last instance - decrement the mtf queue size
        mtf_queue_size[mtf_queue_number]--;
      }
    }
    else {
      mtf_queue_last_ptr = &mtf_queue[mtf_queue_number]
          [(mtf_queue_offset[mtf_queue_number] + mtf_queue_size[mtf_queue_number] - 1) & 0x3F];
      // remove this symbol from its current mtf queue position
      num_az = Symbol + 1;
      mtf_queue_ptr = mtf_queue_last_ptr + 1;
      do {
        if (mtf_queue_ptr != &mtf_queue[mtf_queue_number][0])
          mtf_queue_ptr--;
        else
          mtf_queue_ptr += MTF_QUEUE_SIZE - 1;
        if (symbol_type[*mtf_queue_ptr] & 2)
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
      } while (mtf_queue_ptr != mtf_queue_last_ptr);
      if (--symbols_remaining[symbol_number]) { // put symbol on top of mtf queue
        *mtf_queue_ptr = symbol_number;
        mtf_queue_number -= 2;
        UpFreqMtfQueueNumHitD(CAP);
      }
      else { // last instance - decrement the mtf queue size
        mtf_queue_size[mtf_queue_number]--;
      }
    }
  }
}


#define add_max_length_symbol_to_dictionary(symbol_number) { \
  symbol_index = num_symbols_of_bits[max_code_length]++; \
  symbol_array_of_bits[max_code_length][symbol_index] = symbol_number; \
  symbol_array_index[symbol_number] = symbol_index; \
  if (symbol_index == max_symbols_in_max_code_length_bins) { \
    if (max_code_length >= 12) { \
      start_mtf_codes++; \
      num_bins_of_bits[max_code_length]++; \
      max_symbols_in_max_code_length_bins += max_code_length_symbols_per_bin; \
    } \
    else { \
      start_mtf_codes += 1 << (12 - max_code_length); \
      num_bins_of_bits[max_code_length] += 1 << (12 - max_code_length); \
      max_symbols_in_max_code_length_bins++; \
    } \
  } \
}


#define add_max_length_symbol_to_dictionary_cap(symbol_number) { \
  symbol_index = num_symbols_of_bits_cap[max_code_length]++; \
  symbol_array_of_bits_cap[max_code_length][symbol_index] = symbol_number; \
  symbol_array_index_cap[symbol_number] = symbol_index; \
  if (symbol_index == max_symbols_in_max_code_length_bins_cap) { \
    if (max_code_length >= 12) { \
      start_mtf_codes_cap++; \
      num_bins_of_bits_cap[max_code_length]++; \
      max_symbols_in_max_code_length_bins_cap += max_code_length_symbols_per_bin; \
    } \
    else { \
      start_mtf_codes_cap += 1 << (12 - max_code_length); \
      num_bins_of_bits_cap[max_code_length] += 1 << (12 - max_code_length); \
      max_symbols_in_max_code_length_bins_cap++; \
    } \
  } \
}


#define add_symbol_to_dictionary(symbol_number) { \
  symbol_index = num_symbols_of_bits[define_symbol_code_length]++; \
  symbol_array_of_bits[define_symbol_code_length][symbol_index] = symbol_number; \
  symbol_array_index[symbol_number] = symbol_index; \
  update_code_length_tables(define_symbol_code_length); \
}


#define add_symbol_to_dictionary_cap(symbol_number) { \
  add_symbol_to_dictionary(symbol_number); \
  if (symbol_type[symbol_number] & 2) { \
    update_code_length_tables_cap(define_symbol_code_length, symbol_number); \
  } \
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


unsigned char* decode_define(unsigned char* define_string) {
  unsigned char define_symbol_instances, define_symbol_code_length, *define_string_ptr, *end_define_string_ptr;
  unsigned char nonergodic = 0;
  unsigned int symbols_in_definition;

  end_define_string_ptr = define_string;

  DecodeSID(NOT_CAP);
  symbols_in_definition = SIDSymbol + 1;
  if (symbols_in_definition == 16) {
    get_extra_length();
  }
  DecodeINST(NOT_CAP);
  if (symbols_in_definition == 1) {
    if (Instances >= MAX_INSTANCES_FOR_MTF_QUEUE) {
      define_symbol_instances = 0;
      define_symbol_code_length = max_regular_code_length + MAX_INSTANCES_FOR_MTF_QUEUE - Instances;
      if ((define_symbol_code_length > 10) && (use_mtf || (max_code_length >= 12))) {
        DecodeERG();
      }
    }
    else if (Instances != MAX_INSTANCES_FOR_MTF_QUEUE - 1) {
      define_symbol_instances = Instances + 2;
      define_symbol_code_length = mtf_queue_miss_code_length[define_symbol_instances];
    }
    else
      define_symbol_instances = 1;
    DecodeBaseSymbol(base_bits);
    if (BaseSymbol < START_UTF8_2BYTE_symbols)
      *end_define_string_ptr++ = (unsigned char)BaseSymbol;
    else {
      if (UTF8_compliant) {
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
      else
        *end_define_string_ptr++ = (unsigned char)BaseSymbol;
    }
    if (define_symbol_instances == 1) {
      symbol_string_ptr = symbol_strings + symbol_string_indexes[num_symbols_defined];
      define_string_ptr = define_string;
      while (define_string_ptr != end_define_string_ptr)
        *symbol_string_ptr++ = *define_string_ptr++;
      symbol_string_indexes[++num_symbols_defined] = symbol_string_ptr - symbol_strings;
      return(end_define_string_ptr);
    }
  }
  else {
    if (Instances >= MAX_INSTANCES_FOR_MTF_QUEUE) {
      define_symbol_instances = 0;
      define_symbol_code_length = max_regular_code_length + MAX_INSTANCES_FOR_MTF_QUEUE - Instances;
      if ((define_symbol_code_length > 10) && (use_mtf || (max_code_length >= 12))) {
        DecodeERG();
      }
    }
    else {
      define_symbol_instances = Instances + 2;
      define_symbol_code_length = mtf_queue_miss_code_length[define_symbol_instances];
    }

    do { // Build the symbol string from the next symbols_in_definition symbols
      DecodeSymType(LEVEL1);
      if (Symbol != 1) {
        if (Symbol != 0) {
          if (Symbol == 2) {
            get_mtfg_symbol();
          }
          else {
            get_mtf_symbol();
          }
        }
        else {
          DictionaryBins = start_mtf_codes;
          DecodeDictionaryBin(lookup_bits);
          if (CodeLength > 12) {
            get_long_symbol();
          }
          else {
            get_short_symbol();
          }
          if (symbol_instances[symbol_number] <= 20) {
            if (use_mtf) {
              insert_mtf_queue();
            }
            else {
              check_last_symbol();
            }
          }
          else if (symbol_type[symbol_number] & 4) {
            add_new_symbol_to_mtfg_queue(symbol_number);
          }
        }
        symbol_string_ptr = symbol_strings + symbol_string_indexes[symbol_number];
        next_string_ptr = symbol_strings + symbol_string_indexes[symbol_number + 1];
        symbol_string_ptr = symbol_strings + symbol_string_indexes[symbol_number];
        while (symbol_string_ptr != next_string_ptr)
          *end_define_string_ptr++ = *symbol_string_ptr++;
      }
      else {
        end_define_string_ptr = decode_define(end_define_string_ptr);
      }
    } while (--symbols_in_definition);
  }

  if (define_symbol_instances) { // mtf queue symbol
    if (define_symbol_instances == 2) {
      symbol_instances[num_symbols_defined] = 2;
      symbols_remaining[num_symbols_defined] = 1;
      if (use_mtf) {
        mtf_queue_number = 0;
        UpFreqMtfQueueNumD(NOT_CAP);
        if (mtf_queue_size[2] != MTF_QUEUE_SIZE) // put the symbol in the mtf queue
          mtf_queue[2][(mtf_queue_size[2]++ + mtf_queue_offset[2]) & 0x3F] = num_symbols_defined;
        else { // put last mtf queue symbol in symbol list
          mtf_queue_ptr = &mtf_queue[2][mtf_queue_offset[2]];
          symbol_number = *mtf_queue_ptr;
          add_max_length_symbol_to_dictionary(symbol_number);
          // put symbol in queue and rotate cyclical buffer
          *mtf_queue_ptr = num_symbols_defined;
          mtf_queue_offset[2] = (mtf_queue_offset[2] + 1) & 0x3F;
        }
      }
      else {
        add_max_length_symbol_to_dictionary(num_symbols_defined);
      }
    }
    else {
      symbol_instances[num_symbols_defined] = define_symbol_instances;
      symbols_remaining[num_symbols_defined] = define_symbol_instances - 1;
      if (use_mtf) {
        mtf_queue_number = define_symbol_instances - 2;
        UpFreqMtfQueueNumD(NOT_CAP);
        if (mtf_queue_size[define_symbol_instances] != MTF_QUEUE_SIZE) // put the symbol in the mtf queue
          mtf_queue[define_symbol_instances]
                [(mtf_queue_size[define_symbol_instances]++ + mtf_queue_offset[define_symbol_instances]) & 0x3F]
              = num_symbols_defined;
        else { // put last mtf queue symbol in symbol list
          mtf_queue_ptr = &mtf_queue[define_symbol_instances][mtf_queue_offset[define_symbol_instances]];
          symbol_number = *mtf_queue_ptr;
          add_symbol_to_dictionary(symbol_number);
          // put symbol in queue and rotate cyclical buffer
          *mtf_queue_ptr = num_symbols_defined;
          mtf_queue_offset[define_symbol_instances] = (mtf_queue_offset[define_symbol_instances] + 1) & 0x3F;
        }
      }
      else {
        add_symbol_to_dictionary(num_symbols_defined);
      }
    }
  }
  else { // put symbol in table
    symbol_type[num_symbols_defined] = nonergodic << 2;
    if (nonergodic) {
      add_new_symbol_to_mtfg_queue(num_symbols_defined);
    }
    symbol_instances[num_symbols_defined] = define_symbol_code_length + 20;
    add_symbol_to_dictionary(num_symbols_defined);
  }
  symbol_string_ptr = symbol_strings + symbol_string_indexes[num_symbols_defined];

  define_string_ptr = define_string;
  copy_string(define_string_ptr, end_define_string_ptr, symbol_string_ptr);
  symbol_string_indexes[++num_symbols_defined] = symbol_string_ptr - symbol_strings;
  return(end_define_string_ptr);
}


unsigned char* decode_define_cap_encoded(unsigned char* define_string, unsigned char first_symbol_in_string) {
  unsigned char define_symbol_instances, define_symbol_code_length, *define_string_ptr, *end_define_string_ptr;
  unsigned char char_before_define_is_cap, first_symbol;
  unsigned char nonergodic = 0;
  unsigned int symbols_in_definition;

  char_before_define_is_cap = prior_is_cap;
  caps_on = 0;
  end_define_string_ptr = define_string;

  if (prior_is_cap == 0) {
    DecodeSID(NOT_CAP);
  }
  else {
    DecodeSID(CAP);
  }
  symbols_in_definition = SIDSymbol + 1;
  if (symbols_in_definition == 16) {
    get_extra_length();
  }
  if (prior_is_cap == 0) {
    DecodeINST(NOT_CAP);
  }
  else {
    DecodeINST(CAP);
  }

  if (symbols_in_definition == 1) {
    if (Instances >= MAX_INSTANCES_FOR_MTF_QUEUE) {
      define_symbol_instances = 0;
      define_symbol_code_length = max_regular_code_length + MAX_INSTANCES_FOR_MTF_QUEUE - Instances;
      if ((define_symbol_code_length > 10) && (use_mtf || (max_code_length >= 12))) {
        DecodeERG();
      }
    }
    else if (Instances != MAX_INSTANCES_FOR_MTF_QUEUE - 1) {
      define_symbol_instances = Instances + 2;
      define_symbol_code_length = mtf_queue_miss_code_length[define_symbol_instances];
    }
    else
      define_symbol_instances = 1;
    DecodeBaseSymbol(base_bits);
    if (BaseSymbol < START_UTF8_2BYTE_symbols) {
      if ((unsigned char)BaseSymbol == CAP_CHAR) {
        symbol_type[num_symbols_defined] = (nonergodic << 2) + 1;
        caps_on = 1;
        prior_is_cap = 1;
      }
      else {
        symbol_type[num_symbols_defined] = (nonergodic << 2) + (((BaseSymbol >= 0x61) && (BaseSymbol <= 0x7A)) << 1);
        *end_define_string_ptr++ = (unsigned char)BaseSymbol - 0x20 * caps_on;
        caps_on = 0;
        prior_is_cap = 0;
      }
    }
    else {
      symbol_type[num_symbols_defined] = nonergodic << 2;
      caps_on = 0;
      prior_is_cap = 0;
      if (UTF8_compliant) {
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
      else
        *end_define_string_ptr++ = (unsigned char)BaseSymbol;
    }
    if (define_symbol_instances == 1) {
      symbol_string_ptr = symbol_strings + symbol_string_indexes[num_symbols_defined];
      define_string_ptr = define_string;
      while (define_string_ptr != end_define_string_ptr)
        *symbol_string_ptr++ = *define_string_ptr++;
      symbol_string_indexes[++num_symbols_defined] = symbol_string_ptr - symbol_strings;
      if (char_before_define_is_cap)
        *define_string -= 0x20;
      return(end_define_string_ptr);
    }
  }
  else {
    if (Instances >= MAX_INSTANCES_FOR_MTF_QUEUE) {
      define_symbol_instances = 0;
      define_symbol_code_length = max_regular_code_length + MAX_INSTANCES_FOR_MTF_QUEUE - Instances;
      if ((define_symbol_code_length > 10) && (use_mtf || (max_code_length >= 12))) {
        DecodeERG();
      }
    }
    else {
      define_symbol_instances = Instances + 2;
      define_symbol_code_length = mtf_queue_miss_code_length[define_symbol_instances];
    }

    first_symbol = 1;
    do { // Build the symbol string from the next symbols_in_definition symbols
      if (prior_is_cap == 0) {
        DecodeSymType(LEVEL1);
        if (Symbol != 1) {
          if (Symbol != 0) {
            if (Symbol == 2) {
              get_mtfg_symbol();
            }
            else {
              get_mtf_symbol();
            }
          }
          else {
            DictionaryBins = start_mtf_codes;
            DecodeDictionaryBin(lookup_bits);
            if (CodeLength > 12) {
              get_long_symbol();
            }
            else {
              get_short_symbol();
            }
            if (symbol_instances[symbol_number] <= 20) {
              if (use_mtf) {
                insert_mtf_queue_cap_encoded();
              }
              else {
                check_last_symbol_cap_encoded();
              }
            }
            else if (symbol_type[symbol_number] & 4) {
              add_new_symbol_to_mtfg_queue(symbol_number);
            }
          }
          symbol_string_ptr = symbol_strings + symbol_string_indexes[symbol_number];
          next_string_ptr = symbol_strings + symbol_string_indexes[symbol_number + 1];
          while (symbol_string_ptr != next_string_ptr)
            *end_define_string_ptr++ = *symbol_string_ptr++;
          caps_on = symbol_type[symbol_number] & 1;
          prior_is_cap = caps_on;
        }
        else {
          end_define_string_ptr = decode_define_cap_encoded(end_define_string_ptr,first_symbol);
        }
      }
      else { // prior_is_cap
        DecodeSymType(LEVEL1_CAP);
        if (Symbol != 1) {
          if (Symbol != 0) {
            if (Symbol == 2) {
              get_mtfg_symbol_cap();
            }
            else {
              get_mtf_symbol_cap();
            }
          }
          else {
            DictionaryBins = start_mtf_codes_cap;
            DecodeDictionaryBin(lookup_bits_cap);
            if (CodeLength > 12) {
              get_long_symbol_cap();
            }
            else {
              get_short_symbol_cap();
            }
            if (symbol_instances[symbol_number] <= 20) {
              if (use_mtf) {
                insert_mtf_queue_cap_encoded_cap();
              }
              else {
                check_last_symbol_cap_encoded_cap();
              }
            }
            else if (symbol_type[symbol_number] & 4) {
              add_new_symbol_to_mtfg_queue(symbol_number);
            }
          }
          symbol_string_ptr = symbol_strings + symbol_string_indexes[symbol_number];
          next_string_ptr = symbol_strings + symbol_string_indexes[symbol_number + 1];
          if (caps_on)
            *end_define_string_ptr++ = *symbol_string_ptr++ - 0x20;
          while (symbol_string_ptr != next_string_ptr)
            *end_define_string_ptr++ = *symbol_string_ptr++;
          caps_on = symbol_type[symbol_number] & 1;
          prior_is_cap = caps_on;
        }
        else {
          end_define_string_ptr = decode_define_cap_encoded(end_define_string_ptr,first_symbol);
        }
      }
      first_symbol = 0;
    } while (--symbols_in_definition);
    symbol_type[num_symbols_defined] = (nonergodic << 2) + (((*define_string >= 'a') && (*define_string <= 'z')) << 1) + caps_on;
  }

  if (define_symbol_instances) { // mtf queue symbol
    if (define_symbol_instances == 2) {
      symbol_instances[num_symbols_defined] = 2;
      symbols_remaining[num_symbols_defined] = 1;
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
          mtf_queue_ptr = &mtf_queue[2][mtf_queue_offset[2]];
          symbol_number = *mtf_queue_ptr;
          add_max_length_symbol_to_dictionary(symbol_number);
          if (symbol_type[symbol_number] & 2) { // put last mtf queue symbol in cap symbol list
            add_max_length_symbol_to_dictionary_cap(symbol_number);
          }
          // put symbol in queue and rotate cyclical buffer
          *mtf_queue_ptr = num_symbols_defined;
          mtf_queue_offset[2] = (mtf_queue_offset[2] + 1) & 0x3F;
        }
      }
      else {
        add_max_length_symbol_to_dictionary(num_symbols_defined);
        if (symbol_type[num_symbols_defined] & 2) { // put last mtf queue symbol in cap symbol list
          add_max_length_symbol_to_dictionary_cap(num_symbols_defined);
        }
      }
    }
    else {
      symbol_instances[num_symbols_defined] = define_symbol_instances;
      symbols_remaining[num_symbols_defined] = define_symbol_instances - 1;
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
          mtf_queue_ptr = &mtf_queue[define_symbol_instances][mtf_queue_offset[define_symbol_instances]];
          symbol_number = *mtf_queue_ptr;
          add_symbol_to_dictionary_cap(symbol_number);
          // put symbol in queue and rotate cyclical buffer
          *mtf_queue_ptr = num_symbols_defined;
          mtf_queue_offset[define_symbol_instances] = (mtf_queue_offset[define_symbol_instances] + 1) & 0x3F;
        }
      }
      else {
        add_symbol_to_dictionary_cap(num_symbols_defined);
      }
    }
  }
  else { // put symbol in table
    if (nonergodic) {
      add_new_symbol_to_mtfg_queue(num_symbols_defined);
    }
    symbol_instances[num_symbols_defined] = 20 + define_symbol_code_length;
    add_symbol_to_dictionary_cap(num_symbols_defined);
  }
  symbol_string_ptr = symbol_strings + symbol_string_indexes[num_symbols_defined];
  define_string_ptr = define_string;
  copy_string(define_string_ptr, end_define_string_ptr, symbol_string_ptr);
  symbol_string_indexes[++num_symbols_defined] = symbol_string_ptr - symbol_strings;
  if (char_before_define_is_cap && (first_symbol_in_string == 0))
    *define_string -= 0x20;
  return(end_define_string_ptr);
}


#define write_output_buffer() { \
  fflush(fd_out); \
  chars_to_write = out_char_ptr - start_char_ptr; \
  fwrite(start_char_ptr,1,chars_to_write,fd_out); \
  out_chars += chars_to_write; \
  if (out_char_buffer == 0) { \
    out_char_buffer = 1; \
    out_char_ptr = out_char1; \
    start_char_ptr = out_char_ptr; \
    extra_out_char_ptr = out_char_ptr + CHARS_TO_WRITE; \
  } \
  else { \
    out_char_buffer = 0; \
    out_char_ptr = out_char0; \
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


#define write_single_threaded_output() { \
  if (cap_encoded) { \
    symbol = *symbol_array_ptr; \
    while (symbol != -1) { \
      symbol_string_ptr = symbol_strings + symbol_string_indexes[symbol]; \
      next_symbol_string_ptr = symbol_strings + symbol_string_indexes[symbol + 1]; \
      if (write_caps_on == 1) \
        *out_char_ptr++ = *symbol_string_ptr++ - 0x20; \
      write_caps_on = symbol_type[symbol] & 1; \
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
      symbol_string_ptr = symbol_strings + symbol_string_indexes[symbol]; \
      next_symbol_string_ptr = symbol_strings + symbol_string_indexes[symbol + 1]; \
      *symbol_array_ptr++ = -1; \
      if (symbol_array_ptr == symbol_array_end_ptr) \
        symbol_array_ptr = symbol_array_start_ptr; \
      write_string(); \
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
  volatile unsigned char *symbol_type_array = symbol_type;
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
  out_char_buffer = 0;
  out_char_ptr = out_char0;
  start_char_ptr = out_char0;
  extra_out_char_ptr = out_char0 + CHARS_TO_WRITE;
  while ((*vol_symbol_array_ptr == -1) && (done_parsing == 0));

  if (*cap_encoded_ptr) {
    while ((done_parsing == 0) || (*vol_symbol_array_ptr != -1)) {
      symbol = *vol_symbol_array_ptr;
      while (symbol != -1) {
        symbol_string_ptr = symbol_strings + symbol_string_indexes[symbol];
        next_symbol_string_ptr = symbol_strings + symbol_string_indexes[symbol + 1];
        if (write_caps_on == 1)
          *out_char_ptr++ = *symbol_string_ptr++ - 0x20;
        write_caps_on = symbol_type_array[symbol] & 1;
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
        symbol_string_ptr = symbol_strings + symbol_string_indexes[symbol];
        next_symbol_string_ptr = symbol_strings + symbol_string_indexes[symbol + 1];
        *vol_symbol_array_ptr++ = -1;
        if (vol_symbol_array_ptr == symbol_array_end_ptr)
          vol_symbol_array_ptr = symbol_array_start_ptr;
        write_string();
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
}


#define send_symbol_cap() { \
  prior_is_cap = symbol_type[symbol_number] & 1; \
  send_symbol(); \
}


int main(int argc, char* argv[]) {
  unsigned int *define_symbol_end_ptr;
  unsigned char arg_num, this_char, *string_ptr, *string_end_ptr;
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
    out_char_buffer = 0;
    out_char_ptr = out_char0;
    start_char_ptr = out_char0;
    extra_out_char_ptr = out_char0 + CHARS_TO_WRITE;
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
  symbol_string_indexes[0] = 0;
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
  max_code_length = out_char0[1] + 1;
  max_code_length_symbols_per_bin = 0x2000 >> (25 - max_code_length);
  max_regular_code_length = (out_char0[2] & 0x1F) + 1;
  mtf_queue_miss_code_length[2] = max_code_length;
  mtf_queue_miss_code_length[3] = mtf_queue_miss_code_length[2] - (out_char0[2] >> 7);
  mtf_queue_miss_code_length[4] = mtf_queue_miss_code_length[3] - ((out_char0[2] >> 6) & 1);
  i1 = 7;
  do {
    mtf_queue_miss_code_length[12 - i1] = mtf_queue_miss_code_length[11 - i1] - ((out_char0[3] >> i1) & 1);
  } while (i1--);
  i1 = 7;
  do {
    mtf_queue_miss_code_length[20 - i1] = mtf_queue_miss_code_length[19 - i1] - ((out_char0[4] >> i1) & 1);
  } while (i1--);
  i1 = (unsigned int)max_code_length;
  do {
    num_symbols_of_bits[i1] = 0;
    num_bins_of_bits[i1] = 0;
    first_bin_of_bits[i1] = 0;
  } while (--i1);
  if (max_code_length >= 12) {
    start_mtf_codes = 1;
    max_symbols_in_max_code_length_bins = max_code_length_symbols_per_bin;
    num_bins_of_bits[max_code_length] = 1;
  }
  else {
    start_mtf_codes = 1 << (12 - max_code_length);
    max_symbols_in_max_code_length_bins = 1;
    num_bins_of_bits[max_code_length] = 1 << (12 - max_code_length);
  }
  symbol_array_of_bits[max_code_length][0] = 9999999;
  symbol_type[9999999] = 0;
  num_symbols_of_bits[max_code_length] = 1;
  i1 = 0x1000;
  while (i1--)
    lookup_bits[i1] = max_code_length;
  if (cap_encoded) {
    prior_is_cap = 0;
    i1 = (unsigned int)max_code_length;
    do {
      num_symbols_of_bits_cap[i1] = 0;
      num_bins_of_bits_cap[i1] = 0;
      first_bin_of_bits_cap[i1] = 0;
    } while (--i1);
    start_mtf_codes_cap = start_mtf_codes;
    max_symbols_in_max_code_length_bins_cap = max_symbols_in_max_code_length_bins;
    num_bins_of_bits_cap[max_code_length] = num_bins_of_bits[max_code_length];
    symbol_array_of_bits_cap[max_code_length][0] = 9999999;
    num_symbols_of_bits_cap[max_code_length] = 1;
    i1 = 0x1000;
    while (i1--)
      lookup_bits_cap[i1] = max_code_length;
  }

  for (i1 = 0 ; i1 < 8 ; i1++)
    mtfg_queue_0[i1] = 9999999;
  for (i1 = 0 ; i1 < 8 ; i1++)
    mtfg_queue_8[i1] = 9999999;
  for (i1 = 0 ; i1 < 16 ; i1++)
    mtfg_queue_16[i1] = 9999999;
  for (i1 = 0 ; i1 < 32 ; i1++)
    mtfg_queue_32[i1] = 9999999;
  for (i1 = 0 ; i1 < 64 ; i1++) {
    mtfg_queue_64[i1] = 9999999;
    mtfg_queue_128[i1] = 9999999;
    mtfg_queue_192[i1] = 9999999;
  }

  InitDecoder(fd_in);

  if (num_threads == 2)
    while (output_ready == 0);

  // symbol processing loop
  if (cap_encoded) {
    while (1) {
      if (prior_is_cap == 0) {
        DecodeSymType(LEVEL0);
        if (Symbol == 0) { // dictionary symbol
          DictionaryBins = start_mtf_codes;
          DecodeDictionaryBin(lookup_bits);
          if (CodeLength > 12) {
            get_long_symbol();
          }
          else {
            get_short_symbol();
            if ((CodeLength == max_code_length) && (BinNum == first_bin_of_bits[max_code_length]))
              break; /* EOF */
          }
          send_symbol_cap();
          if (symbol_instances[symbol_number] <= 20) {
            if (use_mtf) {
              insert_mtf_queue_cap_encoded();
            }
            else {
              check_last_symbol_cap_encoded();
            }
          }
          else if (symbol_type[symbol_number] & 4) {
            add_new_symbol_to_mtfg_queue(symbol_number);
          }
        }
        else if (Symbol != 1) {
          if (Symbol == 2) {
            get_mtfg_symbol();
          }
          else {
            get_mtf_symbol();
          }
          send_symbol_cap();
        }
        else {
          decode_define_cap_encoded(new_symbol_string,0);
          out_symbol_array[out_symbol_count++] = num_symbols_defined - 1;
          manage_symbol_stream(out_char_ptr);
        }
      }
      else { // prior_is_cap
        DecodeSymType(LEVEL0_CAP);
        if (Symbol == 0) {
          DictionaryBins = start_mtf_codes_cap;
          DecodeDictionaryBin(lookup_bits_cap);
          if (CodeLength > 12) {
            get_long_symbol_cap();
          }
          else {
            get_short_symbol_cap();
            if ((CodeLength == max_code_length) && (BinNum == first_bin_of_bits_cap[CodeLength]))
              break; /* EOF */
          }
          send_symbol_cap();
          if (symbol_instances[symbol_number] <= 20) {
            if (use_mtf) {
              insert_mtf_queue_cap_encoded_cap();
            }
            else {
              check_last_symbol_cap_encoded_cap();
            }
          }
          else if ((CodeLength > 10) && (symbol_type[symbol_number] & 4)) {
            add_new_symbol_to_mtfg_queue(symbol_number);
          }
        }
        else if (Symbol != 1) {
          if (Symbol == 2) {
            get_mtfg_symbol_cap();
          }
          else {
            get_mtf_symbol_cap();
          }
          send_symbol_cap();
        }
        else {
          decode_define_cap_encoded(new_symbol_string,0);
          out_symbol_array[out_symbol_count++] = num_symbols_defined - 1;
          manage_symbol_stream(out_char_ptr);
        }
      }
    }
  }
  else { // not cap encoded
    while (1) {
      DecodeSymType(LEVEL0);
      if (Symbol == 0) {
        DictionaryBins = start_mtf_codes;
        DecodeDictionaryBin(lookup_bits);
        if (CodeLength > 12) {
          get_long_symbol();
        }
        else {
          get_short_symbol();
          if ((CodeLength == max_code_length) && (BinNum == first_bin_of_bits[max_code_length]))
            break; /* EOF */
        }
        send_symbol();
        if (symbol_instances[symbol_number] <= 20) {
          if (use_mtf) {
            insert_mtf_queue();
          }
          else {
            check_last_symbol();
          }
        }
        else if (symbol_type[symbol_number]) {
          add_new_symbol_to_mtfg_queue(symbol_number);
        }
      }
      else if (Symbol != 1) {
        if (Symbol == 2) {
          get_mtfg_symbol();
          send_symbol();
        }
        else {
          get_mtf_symbol();
          send_symbol();
        }
      }
      else {
        decode_define(new_symbol_string);
        out_symbol_array[out_symbol_count++] = num_symbols_defined - 1;
        manage_symbol_stream(out_char_ptr);
      }
    }
  }
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