/***********************************************************************

Copyright 2014-2016 Kennon Conrad

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
//   Decodes files created by GLZAencode
//
// Usage:
//   GLZAdecode [-t#] <infilename> <outfilename>, where # is 1 or 2 and is the number of threads

#include <inttypes.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#define decode

const uint32_t START_UTF8_2BYTE_symbols = 0x80;
const uint32_t START_UTF8_3BYTE_symbols = 0x800;
const uint32_t START_UTF8_4BYTE_symbols = 0x10000;
const uint32_t MAX_INSTANCES_FOR_MTF_QUEUE = 15;
const uint32_t MTF_QUEUE_SIZE = 64;
const uint32_t CHARS_TO_WRITE = 0x40000;
const uint32_t MAX_SYMBOLS_DEFINED = 0x00900000;
const uint32_t MAX_U32_VALUE = 0xFFFFFFFF;
const uint16_t FREE_SYMBOL_LIST_SIZE = 0x400;
const uint8_t FREE_STRING_LIST_SIZE = 0x40;
const uint8_t FREE_SYMBOL_LIST_WAIT_SIZE = 0x40;

uint32_t num_symbols_defined, symbol, symbol_number, base_symbol, num_base_symbols, dictionary_size;
uint32_t out_chars, chars_to_write, symbol_index, symbol_to_move, min_extra_reduce_index;
uint32_t mtf_queue[16][64];
uint32_t mtfg_queue_0[8], mtfg_queue_8[8], mtfg_queue_16[0x10], mtfg_queue_32[0x20];
uint32_t mtfg_queue_64[0x40], mtfg_queue_128[0x40], mtfg_queue_192[0x40];
uint32_t nsob[0x100][26];
uint32_t *mtf_queue_ptr, *mtf_queue_top_ptr;
uint32_t *sym_list_ptrs[0x100][26];
uint32_t free_symbol_list[0x400], free_symbol_list_wait1[0x40], free_symbol_list_wait2[0x40];
uint32_t symbol_buffer[0x200];
uint16_t free_symbol_list_length, symbol_buffer_write_index, symbol_buffer_read_index;
uint16_t nbob[0x100][26], sum_nbob[0x100], fbob[0x100][26];
uint8_t symbol_count, max_code_length, max_regular_code_length, find_first_symbol, end_symbol;
uint8_t UTF8_compliant, base_bits, cap_encoded, use_mtf, use_mtfg, prior_is_cap, two_threads;
uint8_t write_cap_on, write_cap_lock_on, skip_space_on, delta_on, delta_format, stride;
uint8_t out_buffer_num, out_buffers_sent, prior_end, no_embed, cap_symbol_defined, cap_lock_symbol_defined;
uint8_t mtfg_queue_0_offset, mtfg_queue_8_offset, mtfg_queue_16_offset, mtfg_queue_32_offset;
uint8_t mtfg_queue_64_offset, mtfg_queue_128_offset, mtfg_queue_192_offset;
uint8_t free_symbol_list_wait1_length, free_symbol_list_wait2_length;
uint8_t free_string_list_length, free_string_list_wait1, free_string_list_wait2;
uint8_t symbol_lengths[0x100], bin_code_length[0x100];
uint8_t out_char0[0x40064], out_char1[0x40064], out_char2[0x30000];
uint8_t mtf_queue_miss_code_length[16], mtf_queue_size[16], mtf_queue_offset[16];
uint8_t *symbol_string_ptr, *next_string_ptr, *out_char_ptr, *start_char_ptr, *extra_out_char_ptr;
uint8_t *symbol_strings;
uint8_t lookup_bits[0x100][0x1000], sym_list_bits[0x100][26];
atomic_uchar done_parsing, symbol_buffer_pt1_owner, symbol_buffer_pt2_owner;
FILE *fd_in, *fd_out;

struct sym_data {
  uint8_t type;  // bit 0: removable, bit1: string starts a-z, bit2: nonergodic, bit3: in queue
      // bit 4: "word", bit 5: non-"word", bit 6: likely to be followed by ' ', bit 7: not likely to be followed by ' '
  uint8_t instances;
  uint8_t remaining;
  uint8_t ends;
  uint32_t string_index;
  uint32_t string_length;
  uint32_t dictionary_index;
} symbol_data[0x00900000];

struct free_str_list {
  uint32_t string_index;
  uint32_t string_length;
  uint8_t wait_cycles;
} free_string_list[0x40];



#include "GLZAmodel.h"


void check_free_symbol() {
  if (symbol_data[symbol_number].type & 1) {
    symbol_data[symbol_number].type &= 0xFE;
    uint32_t symbol_strings_index = symbol_data[symbol_number].string_index;
    uint32_t len = symbol_data[symbol_number].string_length;
    if ((free_string_list_length < FREE_STRING_LIST_SIZE)
        || ((len > free_string_list[FREE_STRING_LIST_SIZE - 1].string_length) && (free_string_list_wait2 < 0x10))) {
      uint8_t free_string_list_index;
      if (free_string_list_length < FREE_STRING_LIST_SIZE)
        free_string_list_index = free_string_list_length++;
      else
        free_string_list_index = FREE_STRING_LIST_SIZE - 1;
      while (free_string_list_index && (len > free_string_list[free_string_list_index - 1].string_length)) {
        free_string_list[free_string_list_index].string_index = free_string_list[free_string_list_index - 1].string_index;
        free_string_list[free_string_list_index].string_length = free_string_list[free_string_list_index - 1].string_length;
        free_string_list[free_string_list_index].wait_cycles = free_string_list[free_string_list_index - 1].wait_cycles;
        free_string_list_index--;
      }
      free_string_list[free_string_list_index].string_index = symbol_strings_index;
      free_string_list[free_string_list_index].string_length = len;
      free_string_list[free_string_list_index].wait_cycles = 2;
      free_string_list_wait2++;
    }
    else if (len > free_string_list[FREE_STRING_LIST_SIZE - 1].string_length) {
      uint8_t free_string_list_index = free_string_list_length - 1;
      while (free_string_list[free_string_list_index].wait_cycles != 2)
        free_string_list_index--;
      if (len > free_string_list[free_string_list_index].string_length) {
        while (free_string_list_index && (len > free_string_list[free_string_list_index - 1].string_length)) {
          free_string_list[free_string_list_index].string_index = free_string_list[free_string_list_index - 1].string_index;
          free_string_list[free_string_list_index].string_length = free_string_list[free_string_list_index - 1].string_length;
          free_string_list[free_string_list_index].wait_cycles = free_string_list[free_string_list_index - 1].wait_cycles;
          free_string_list_index--;
        }
        free_string_list[free_string_list_index].string_index = symbol_strings_index;
        free_string_list[free_string_list_index].string_length = len;
        free_string_list[free_string_list_index].wait_cycles = 2;
        free_string_list_wait2++;
      }
    }
  }
  if (free_symbol_list_wait2_length < FREE_SYMBOL_LIST_WAIT_SIZE)
   free_symbol_list_wait2[free_symbol_list_wait2_length++] = symbol_number;
  return;
}


void remove_mtfg_queue_symbol_16() {
  while (mtfg_queue_position != 31) {
    *(mtfg_queue_16 + ((mtfg_queue_16_offset + mtfg_queue_position) & 0xF))
        = *(mtfg_queue_16 + ((mtfg_queue_16_offset + mtfg_queue_position + 1) & 0xF));
    mtfg_queue_position++;
  }
  *(mtfg_queue_16 + ((mtfg_queue_16_offset - 1) & 0xF)) = *(mtfg_queue_32 + mtfg_queue_32_offset);
  *(mtfg_queue_32 + mtfg_queue_32_offset) = *(mtfg_queue_64 + mtfg_queue_64_offset);
  mtfg_queue_32_offset = (mtfg_queue_32_offset + 1) & 0x1F;
  *(mtfg_queue_64 + mtfg_queue_64_offset) = *(mtfg_queue_128 + mtfg_queue_128_offset);
  mtfg_queue_64_offset = (mtfg_queue_64_offset + 1) & 0x3F;
  *(mtfg_queue_128 + mtfg_queue_128_offset) = *(mtfg_queue_192 + mtfg_queue_192_offset);
  mtfg_queue_128_offset = (mtfg_queue_128_offset + 1) & 0x3F;
  *(mtfg_queue_192 + mtfg_queue_192_offset) = MAX_SYMBOLS_DEFINED - 1;
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F;
  return;
}


void remove_mtfg_queue_symbol_32() {
  while (mtfg_queue_position != 63) {
    *(mtfg_queue_32 + ((mtfg_queue_32_offset + mtfg_queue_position) & 0x1F))
        = *(mtfg_queue_32 + ((mtfg_queue_32_offset + mtfg_queue_position + 1) & 0x1F));
    mtfg_queue_position++;
  }
  *(mtfg_queue_32 + ((mtfg_queue_32_offset - 1) & 0x1F)) = *(mtfg_queue_64 + mtfg_queue_64_offset);
  *(mtfg_queue_64 + mtfg_queue_64_offset) = *(mtfg_queue_128 + mtfg_queue_128_offset);
  mtfg_queue_64_offset = (mtfg_queue_64_offset + 1) & 0x3F;
  *(mtfg_queue_128 + mtfg_queue_128_offset) = *(mtfg_queue_192 + mtfg_queue_192_offset);
  mtfg_queue_128_offset = (mtfg_queue_128_offset + 1) & 0x3F;
  *(mtfg_queue_192 + mtfg_queue_192_offset) = MAX_SYMBOLS_DEFINED - 1;
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F;
  return;
}


void remove_mtfg_queue_symbol_64() {
  while (mtfg_queue_position != 127) {
    *(mtfg_queue_64 + ((mtfg_queue_64_offset + mtfg_queue_position) & 0x3F))
        = *(mtfg_queue_64 + ((mtfg_queue_64_offset + mtfg_queue_position + 1) & 0x3F));
    mtfg_queue_position++;
  }
  *(mtfg_queue_64 + ((mtfg_queue_64_offset - 1) & 0x3F)) = *(mtfg_queue_128 + mtfg_queue_128_offset);
  *(mtfg_queue_128 + mtfg_queue_128_offset) = *(mtfg_queue_192 + mtfg_queue_192_offset);
  mtfg_queue_128_offset = (mtfg_queue_128_offset + 1) & 0x3F;
  *(mtfg_queue_192 + mtfg_queue_192_offset) = MAX_SYMBOLS_DEFINED - 1;
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F;
  return;
}


void remove_mtfg_queue_symbol_128() {
  while (mtfg_queue_position != 191) {
    *(mtfg_queue_128 + ((mtfg_queue_128_offset + mtfg_queue_position) & 0x3F))
        = *(mtfg_queue_128 + ((mtfg_queue_128_offset + mtfg_queue_position + 1) & 0x3F));
    mtfg_queue_position++;
  }
  *(mtfg_queue_128 + ((mtfg_queue_128_offset - 1) & 0x3F)) = *(mtfg_queue_192 + mtfg_queue_192_offset);
  *(mtfg_queue_192 + mtfg_queue_192_offset) = MAX_SYMBOLS_DEFINED - 1;
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F;
  return;
}


void remove_mtfg_queue_symbol_192() {
  while (mtfg_queue_position != 255) {
    *(mtfg_queue_192 + ((mtfg_queue_192_offset + mtfg_queue_position) & 0x3F))
        = *(mtfg_queue_192 + ((mtfg_queue_192_offset + mtfg_queue_position + 1) & 0x3F));
    mtfg_queue_position++;
  }
  *(mtfg_queue_192 + ((mtfg_queue_192_offset - 1) & 0x3F)) = MAX_SYMBOLS_DEFINED - 1;
  return;
}


void add_new_symbol_to_mtfg_queue(uint32_t symbol_number) {
  symbol_data[symbol_number].type |= 8;
  mtfg_queue_8_offset = (mtfg_queue_8_offset - 1) & 7;
  uint32_t mtfg_queue_symbol_15 = *(mtfg_queue_8 + mtfg_queue_8_offset);
  mtfg_queue_0_offset = (mtfg_queue_0_offset - 1) & 7;
  *(mtfg_queue_8 + mtfg_queue_8_offset) = *(mtfg_queue_0 + mtfg_queue_0_offset);
  *(mtfg_queue_0 + mtfg_queue_0_offset) = symbol_number;
  if (symbol_data[mtfg_queue_symbol_15].instances - MAX_INSTANCES_FOR_MTF_QUEUE > 12) {
    mtfg_queue_16_offset = (mtfg_queue_16_offset - 1) & 0xF;
    uint32_t mtfg_queue_symbol_31 = *(mtfg_queue_16 + mtfg_queue_16_offset);
    *(mtfg_queue_16 + mtfg_queue_16_offset) = mtfg_queue_symbol_15;
    if (symbol_data[mtfg_queue_symbol_31].instances - MAX_INSTANCES_FOR_MTF_QUEUE != 13) {
      mtfg_queue_32_offset = (mtfg_queue_32_offset - 1) & 0x1F;
      uint32_t mtfg_queue_symbol_63 = *(mtfg_queue_32 + mtfg_queue_32_offset);
      *(mtfg_queue_32 + mtfg_queue_32_offset) = mtfg_queue_symbol_31;
      if (symbol_data[mtfg_queue_symbol_63].instances - MAX_INSTANCES_FOR_MTF_QUEUE != 14) {
        mtfg_queue_64_offset = (mtfg_queue_64_offset - 1) & 0x3F;
        uint32_t mtfg_queue_symbol_127 = *(mtfg_queue_64 + mtfg_queue_64_offset);
        *(mtfg_queue_64 + mtfg_queue_64_offset) = mtfg_queue_symbol_63;
        if (symbol_data[mtfg_queue_symbol_127].instances - MAX_INSTANCES_FOR_MTF_QUEUE != 15) {
          mtfg_queue_128_offset = (mtfg_queue_128_offset - 1) & 0x3F;
          uint32_t mtfg_queue_symbol_191 = *(mtfg_queue_128 + mtfg_queue_128_offset);
          *(mtfg_queue_128 + mtfg_queue_128_offset) = mtfg_queue_symbol_127;
          if (symbol_data[mtfg_queue_symbol_191].instances - MAX_INSTANCES_FOR_MTF_QUEUE != 16) {
            mtfg_queue_192_offset = (mtfg_queue_192_offset - 1) & 0x3F;
            symbol_data[*(mtfg_queue_192 + mtfg_queue_192_offset)].type &= 0xF7;
            *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191;
          }
          else
            symbol_data[mtfg_queue_symbol_191].type &= 0xF7;
        }
        else
          symbol_data[mtfg_queue_symbol_127].type &= 0xF7;
      }
      else
        symbol_data[mtfg_queue_symbol_63].type &= 0xF7;
    }
    else
      symbol_data[mtfg_queue_symbol_31].type &= 0xF7;
  }
  else
    symbol_data[mtfg_queue_symbol_15].type &= 0xF7;
  return;
}


void update_mtfg_queue() {
  uint32_t mtfg_queue_symbol_15, mtfg_queue_symbol_31, mtfg_queue_symbol_63, mtfg_queue_symbol_127, mtfg_queue_symbol_191;
  if (mtfg_queue_position < 8) {
    symbol_number = mtfg_queue_0[(mtfg_queue_position += mtfg_queue_0_offset) & 7];
    while (mtfg_queue_position != mtfg_queue_0_offset) {
      *(mtfg_queue_0 + (mtfg_queue_position & 7)) = *(mtfg_queue_0 + ((mtfg_queue_position - 1) & 7));
      mtfg_queue_position--;
    }
  }
  else if (mtfg_queue_position < 16) {
    symbol_number = *(mtfg_queue_8 + ((mtfg_queue_position += mtfg_queue_8_offset - 8) & 7));
    while (mtfg_queue_position != mtfg_queue_8_offset) {
      *(mtfg_queue_8 + (mtfg_queue_position & 7)) = *(mtfg_queue_8 + ((mtfg_queue_position - 1) & 7));
      mtfg_queue_position--;
    }
    mtfg_queue_0_offset = (mtfg_queue_0_offset - 1) & 7;
    *(mtfg_queue_8 + mtfg_queue_8_offset) = *(mtfg_queue_0 + mtfg_queue_0_offset);
  }
  else {
    mtfg_queue_0_offset = (mtfg_queue_0_offset - 1) & 7;
    mtfg_queue_8_offset = (mtfg_queue_8_offset - 1) & 7;
    mtfg_queue_symbol_15 = *(mtfg_queue_8 + mtfg_queue_8_offset);
    *(mtfg_queue_8 + mtfg_queue_8_offset) = *(mtfg_queue_0 + mtfg_queue_0_offset);
    if (symbol_data[mtfg_queue_symbol_15].instances - MAX_INSTANCES_FOR_MTF_QUEUE <= 12) {
      symbol_data[mtfg_queue_symbol_15].type &= 0xF7;
      if (mtfg_queue_position < 32) {
        symbol_number = *(mtfg_queue_16 + ((mtfg_queue_position + mtfg_queue_16_offset) & 0xF));
        remove_mtfg_queue_symbol_16();
      }
      else if (mtfg_queue_position < 64) {
        symbol_number = *(mtfg_queue_32 + ((mtfg_queue_position + mtfg_queue_32_offset) & 0x1F));
        remove_mtfg_queue_symbol_32();
      }
      else if (mtfg_queue_position < 128) {
        symbol_number = *(mtfg_queue_64 + ((mtfg_queue_position + mtfg_queue_64_offset) & 0x3F));
        remove_mtfg_queue_symbol_64();
      }
      else if (mtfg_queue_position < 192) {
        symbol_number = *(mtfg_queue_128 + ((mtfg_queue_position + mtfg_queue_128_offset) & 0x3F));
        remove_mtfg_queue_symbol_128();
      }
      else {
        symbol_number = *(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F));
        remove_mtfg_queue_symbol_192();
      }
    }
    else if (mtfg_queue_position < 32) {
      symbol_number = *(mtfg_queue_16 + ((mtfg_queue_position + mtfg_queue_16_offset) & 0xF));
      mtfg_queue_position += mtfg_queue_16_offset - 16;
      while (mtfg_queue_position != mtfg_queue_16_offset) {
        *(mtfg_queue_16 + (mtfg_queue_position & 0xF)) = *(mtfg_queue_16 + ((mtfg_queue_position - 1) & 0xF));
        mtfg_queue_position--;
      }
      *(mtfg_queue_16 + mtfg_queue_16_offset) = mtfg_queue_symbol_15;
    }
    else {
      mtfg_queue_16_offset = (mtfg_queue_16_offset - 1) & 0xF;
      mtfg_queue_symbol_31 = *(mtfg_queue_16 + mtfg_queue_16_offset);
      *(mtfg_queue_16 + mtfg_queue_16_offset) = mtfg_queue_symbol_15;
      if (symbol_data[mtfg_queue_symbol_31].instances - MAX_INSTANCES_FOR_MTF_QUEUE == 13) {
        symbol_data[mtfg_queue_symbol_31].type &= 0xF7;
        if (mtfg_queue_position < 64) {
          symbol_number = *(mtfg_queue_32 + ((mtfg_queue_position + mtfg_queue_32_offset) & 0x1F));
          remove_mtfg_queue_symbol_32();
        }
        else if (mtfg_queue_position < 128) {
          symbol_number = *(mtfg_queue_64 + ((mtfg_queue_position + mtfg_queue_64_offset) & 0x3F));
          remove_mtfg_queue_symbol_64();
        }
        else if (mtfg_queue_position < 192) {
          symbol_number = *(mtfg_queue_128 + ((mtfg_queue_position + mtfg_queue_128_offset) & 0x3F));
          remove_mtfg_queue_symbol_128();
        }
        else {
          symbol_number = *(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F));
          remove_mtfg_queue_symbol_192();
        }
      }
      else if (mtfg_queue_position < 64) {
        symbol_number = *(mtfg_queue_32 + ((mtfg_queue_position + mtfg_queue_32_offset) & 0x1F));
        mtfg_queue_position += mtfg_queue_32_offset - 32;
        while (mtfg_queue_position != mtfg_queue_32_offset) {
          *(mtfg_queue_32 + (mtfg_queue_position & 0x1F)) = *(mtfg_queue_32 + ((mtfg_queue_position - 1) & 0x1F));
          mtfg_queue_position--;
        }
        *(mtfg_queue_32 + mtfg_queue_32_offset) = mtfg_queue_symbol_31;
      }
      else {
        mtfg_queue_32_offset = (mtfg_queue_32_offset - 1) & 0x1F;
        mtfg_queue_symbol_63 = *(mtfg_queue_32 + mtfg_queue_32_offset);
        *(mtfg_queue_32 + mtfg_queue_32_offset) = mtfg_queue_symbol_31;
        if (symbol_data[mtfg_queue_symbol_63].instances - MAX_INSTANCES_FOR_MTF_QUEUE == 14) {
          symbol_data[mtfg_queue_symbol_63].type &= 0xF7;
          if (mtfg_queue_position < 128) {
            symbol_number = *(mtfg_queue_64 + ((mtfg_queue_position + mtfg_queue_64_offset) & 0x3F));
            remove_mtfg_queue_symbol_64();
          }
          else if (mtfg_queue_position < 192) {
            symbol_number = *(mtfg_queue_128 + ((mtfg_queue_position + mtfg_queue_128_offset) & 0x3F));
            remove_mtfg_queue_symbol_128();
          }
          else {
            symbol_number = *(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F));
            remove_mtfg_queue_symbol_192();
          }
        }
        else if (mtfg_queue_position < 128) {
          symbol_number = *(mtfg_queue_64 + ((mtfg_queue_position + mtfg_queue_64_offset) & 0x3F));
          mtfg_queue_position += mtfg_queue_64_offset - 64;
          while (mtfg_queue_position != mtfg_queue_64_offset) {
            *(mtfg_queue_64 + (mtfg_queue_position & 0x3F)) = *(mtfg_queue_64 + ((mtfg_queue_position - 1) & 0x3F));
            mtfg_queue_position--;
          }
          *(mtfg_queue_64 + mtfg_queue_64_offset) = mtfg_queue_symbol_63;
        }
        else {
          mtfg_queue_64_offset = (mtfg_queue_64_offset - 1) & 0x3F;
          mtfg_queue_symbol_127 = *(mtfg_queue_64 + mtfg_queue_64_offset);
          *(mtfg_queue_64 + mtfg_queue_64_offset) = mtfg_queue_symbol_63;
          if (symbol_data[mtfg_queue_symbol_127].instances - MAX_INSTANCES_FOR_MTF_QUEUE == 15) {
            symbol_data[mtfg_queue_symbol_127].type &= 0xF7;
            if (mtfg_queue_position < 192) {
              symbol_number = *(mtfg_queue_128 + ((mtfg_queue_position + mtfg_queue_128_offset) & 0x3F));
              remove_mtfg_queue_symbol_128();
            }
            else {
              symbol_number = *(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F));
              remove_mtfg_queue_symbol_192();
            }
          }
          else if (mtfg_queue_position < 192) {
            symbol_number = *(mtfg_queue_128 + ((mtfg_queue_position + mtfg_queue_128_offset) & 0x3F));
            mtfg_queue_position += mtfg_queue_128_offset - 128;
            while (mtfg_queue_position != mtfg_queue_128_offset) {
              *(mtfg_queue_128 + (mtfg_queue_position & 0x3F)) = *(mtfg_queue_128 + ((mtfg_queue_position - 1) & 0x3F));
              mtfg_queue_position--;
            }
            *(mtfg_queue_128 + mtfg_queue_128_offset) = mtfg_queue_symbol_127;
          }
          else {
            symbol_number = *(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F));
            mtfg_queue_128_offset = (mtfg_queue_128_offset - 1) & 0x3F;
            mtfg_queue_symbol_191 = *(mtfg_queue_128 + mtfg_queue_128_offset);
           *(mtfg_queue_128 + mtfg_queue_128_offset) = mtfg_queue_symbol_127;
            if (symbol_data[mtfg_queue_symbol_191].instances - MAX_INSTANCES_FOR_MTF_QUEUE == 16) {
              symbol_data[mtfg_queue_symbol_191].type &= 0xF7;
              remove_mtfg_queue_symbol_192();
            }
            else {
              mtfg_queue_position += mtfg_queue_192_offset - 192;
              while (mtfg_queue_position != mtfg_queue_192_offset) {
                *(mtfg_queue_192 + (mtfg_queue_position & 0x3F)) = *(mtfg_queue_192 + ((mtfg_queue_position - 1) & 0x3F));
                mtfg_queue_position--;
              }
              *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191;
            }
          }
        }
      }
    }
  }
  *(mtfg_queue_0 + mtfg_queue_0_offset) = symbol_number;
  return;
}


void get_mtfg_symbol() {
  DecodeMtfgQueuePosStart(NOT_CAP);
  if (DecodeMtfgQueuePosCheck0(NOT_CAP)) {
    DecodeMtfgQueuePosFinish0(NOT_CAP);
  }
  else {
    DecodeMtfgQueuePosFinish(NOT_CAP);
  }
  update_mtfg_queue();
  return;
}


#define process_cap_mtfg_position0(mtfg_queue, position_mask) { \
  if (symbol_data[*(mtfg_queue + cap_queue_position)].type & 2) { \
    update_mtfg_queue(); \
    return; \
  } \
  else \
    mtfg_queue_position++; \
  cap_queue_position = (cap_queue_position + 1) & position_mask; \
}


#define process_cap_mtfg_position(mtfg_queue, position_mask) { \
  if (symbol_data[*(mtfg_queue + cap_queue_position)].type & 2) { \
    if (--find_caps == 0) { \
      update_mtfg_queue(); \
      return; \
    } \
  } \
  else \
    mtfg_queue_position++; \
  cap_queue_position = (cap_queue_position + 1) & position_mask; \
}


void get_mtfg_symbol_cap() {
  DecodeMtfgQueuePosStart(CAP);
  if (DecodeMtfgQueuePosCheck0(CAP)) {
    DecodeMtfgQueuePosFinish0(CAP);
    uint8_t find_caps = 1;
    uint8_t cap_queue_position = mtfg_queue_0_offset;
    do {
      process_cap_mtfg_position0(mtfg_queue_0, 7);
    } while (cap_queue_position != mtfg_queue_0_offset);
    if (find_caps) {
      cap_queue_position = mtfg_queue_8_offset;
      do {
        process_cap_mtfg_position0(mtfg_queue_8, 7);
      } while (cap_queue_position != mtfg_queue_8_offset);
      if (find_caps) {
        cap_queue_position = mtfg_queue_16_offset;
        do {
          process_cap_mtfg_position0(mtfg_queue_16, 0xF);
        } while (cap_queue_position != mtfg_queue_16_offset);
        if (find_caps) {
          cap_queue_position = mtfg_queue_32_offset;
          do {
            process_cap_mtfg_position0(mtfg_queue_32, 0x1F);
          } while (cap_queue_position != mtfg_queue_32_offset);
          if (find_caps) {
            cap_queue_position = mtfg_queue_64_offset;
            do {
              process_cap_mtfg_position0(mtfg_queue_64, 0x3F);
            } while (cap_queue_position != mtfg_queue_64_offset);
            if (find_caps) {
              cap_queue_position = mtfg_queue_128_offset;
              do {
                process_cap_mtfg_position0(mtfg_queue_128, 0x3F);
              } while (cap_queue_position != mtfg_queue_128_offset);
              if (find_caps) {
                cap_queue_position = mtfg_queue_192_offset;
                while ((symbol_data[*(mtfg_queue_192 + cap_queue_position)].type & 2) == 0) {
                  mtfg_queue_position++;
                  cap_queue_position = (cap_queue_position + 1) & 0x3F;
                }
              }
            }
          }
        }
      }
    }
  }
  else {
    DecodeMtfgQueuePosFinish(CAP);
    uint8_t find_caps = mtfg_queue_position + 1;
    uint8_t cap_queue_position = mtfg_queue_0_offset;
    do {
      process_cap_mtfg_position(mtfg_queue_0, 7);
    } while (cap_queue_position != mtfg_queue_0_offset);
    if (find_caps) {
      cap_queue_position = mtfg_queue_8_offset;
      do {
        process_cap_mtfg_position(mtfg_queue_8, 7);
      } while (cap_queue_position != mtfg_queue_8_offset);
      if (find_caps) {
        cap_queue_position = mtfg_queue_16_offset;
        do {
          process_cap_mtfg_position(mtfg_queue_16, 0xF);
        } while (cap_queue_position != mtfg_queue_16_offset);
        if (find_caps) {
          cap_queue_position = mtfg_queue_32_offset;
          do {
            process_cap_mtfg_position(mtfg_queue_32, 0x1F);
          } while (cap_queue_position != mtfg_queue_32_offset);
          if (find_caps) {
            cap_queue_position = mtfg_queue_64_offset;
            do {
              process_cap_mtfg_position(mtfg_queue_64, 0x3F);
            } while (cap_queue_position != mtfg_queue_64_offset);
            if (find_caps) {
              cap_queue_position = mtfg_queue_128_offset;
              do {
                process_cap_mtfg_position(mtfg_queue_128, 0x3F);
              } while (cap_queue_position != mtfg_queue_128_offset);
              if (find_caps) {
                cap_queue_position = mtfg_queue_192_offset;
                do {
                  if (symbol_data[*(mtfg_queue_192 + cap_queue_position)].type & 2) {
                    if (--find_caps == 0)
                      break;
                  }
                  else
                    mtfg_queue_position++;
                  cap_queue_position = (cap_queue_position + 1) & 0x3F;
                } while (1);
              }
            }
          }
        }
      }
    }
  }
  update_mtfg_queue();
  return;
}


void add_dictionary_symbol(uint32_t symbol, uint8_t bits) {
  uint8_t first_char = symbol_strings[symbol_data[symbol].string_index];
  if (UTF8_compliant && (first_char > 0x80))
    first_char = 0x80;
  if (nsob[first_char][bits] == ((uint32_t)1 << sym_list_bits[first_char][bits])) {
    sym_list_bits[first_char][bits]++;
    if (0 == (sym_list_ptrs[first_char][bits]
        = (uint32_t *)realloc(sym_list_ptrs[first_char][bits], sizeof(uint32_t) * (1 << sym_list_bits[first_char][bits])))) {
      fprintf(stderr,"FATAL ERROR - symbol list realloc failure\n");
      exit(EXIT_FAILURE);
    }
  }
  symbol_data[symbol].dictionary_index = nsob[first_char][bits];
  sym_list_ptrs[first_char][bits][nsob[first_char][bits]++] = symbol;
  if ((nsob[first_char][bits] << (32 - bits)) > ((uint32_t)nbob[first_char][bits] << (32 - bin_code_length[first_char]))) {
    if (bits >= bin_code_length[first_char]) { /* add a bin */
      if (++sum_nbob[first_char] <= 0x1000) {
        if (bits == max_code_length)
          nbob[first_char][bits]++;
        else {
          lookup_bits[first_char][fbob[first_char][bits] + nbob[first_char][bits]++] = bits;
          uint8_t temp_bits = bits;
          while (++temp_bits != max_code_length) {
            if (nbob[first_char][temp_bits])
              lookup_bits[first_char][fbob[first_char][temp_bits] + nbob[first_char][temp_bits]] = temp_bits;
            fbob[first_char][temp_bits]++;
          }
          fbob[first_char][max_code_length]++;
        }
      }
      else {
        nbob[first_char][bits]++;
        uint8_t code_length;
        do {
          bin_code_length[first_char]--;
          sum_nbob[first_char] = 0;
          for (code_length = 1 ; code_length <= max_code_length ; code_length++)
            sum_nbob[first_char] += (nbob[first_char][code_length] = (nbob[first_char][code_length] + 1) >> 1);
        } while (sum_nbob[first_char] > 0x1000);
        uint16_t bin = nbob[first_char][1];
        uint8_t temp_bits;
        for (temp_bits = 1 ; temp_bits <= max_code_length ; temp_bits++) {
          fbob[first_char][temp_bits] = bin;
          bin += nbob[first_char][temp_bits];
        }
        bin = 0;
        for (code_length = 1 ; code_length < max_code_length ; code_length++)
          while (bin < fbob[first_char][code_length+1])
            lookup_bits[first_char][bin++] = code_length;
        while (bin < 0x1000)
          lookup_bits[first_char][bin++] = max_code_length;
      }
    }
    else { /* add multiple bins */
      uint32_t new_bins = 1 << (bin_code_length[first_char] - bits);
      if (sum_nbob[first_char] + new_bins <= 0x1000) {
        sum_nbob[first_char] += new_bins;
        do {
          lookup_bits[first_char][fbob[first_char][bits] + nbob[first_char][bits]] = bits;
          nbob[first_char][bits]++;
          uint8_t temp_bits = bits;
          while (++temp_bits != max_code_length) {
            if (nbob[first_char][temp_bits])
              lookup_bits[first_char][fbob[first_char][temp_bits] + nbob[first_char][temp_bits]] = temp_bits;
            fbob[first_char][temp_bits]++;
          }
        } while ((nsob[first_char][bits] << (bin_code_length[first_char] - bits)) > (uint32_t)nbob[first_char][bits]);
        fbob[first_char][max_code_length] += 1 << (bin_code_length[first_char] - bits);
      }
      else if (new_bins <= 0x1000) {
        nbob[first_char][bits] += new_bins;
        uint8_t code_length;
        do {
          bin_code_length[first_char]--;
          sum_nbob[first_char] = 0;
          for (code_length = 1 ; code_length <= max_code_length ; code_length++)
            sum_nbob[first_char] += (nbob[first_char][code_length] = (nbob[first_char][code_length] + 1) >> 1);
        } while (sum_nbob[first_char] > 0x1000);
        uint16_t bin = nbob[first_char][1];
        uint8_t temp_bits;
        for (temp_bits = 2 ; temp_bits <= max_code_length ; temp_bits++) {
          fbob[first_char][temp_bits] = bin;
          bin += nbob[first_char][temp_bits];
        }
        bin = 0;
        for (code_length = 1 ; code_length < max_code_length ; code_length++)
          while (bin < fbob[first_char][code_length+1])
            lookup_bits[first_char][bin++] = code_length;
        while (bin < 0x1000)
          lookup_bits[first_char][bin++] = max_code_length;
      }
      else {
        uint8_t bin_shift = bin_code_length[first_char] - 12 - bits;
        if (sum_nbob[first_char])
          bin_shift++;
        bin_code_length[first_char] -= bin_shift;
        sum_nbob[first_char] = 0;
        uint8_t code_length;
        for (code_length = 1 ; code_length <= max_code_length ; code_length++)
          sum_nbob[first_char] += (nbob[first_char][code_length]
              = (nbob[first_char][code_length] + (1 << bin_shift) - 1) >> bin_shift);
        nbob[first_char][bits] += new_bins >> bin_shift;
        sum_nbob[first_char] += new_bins >> bin_shift;
        uint16_t bin = nbob[first_char][1];
        uint8_t temp_bits;
        for (temp_bits = 1 ; temp_bits <= max_code_length ; temp_bits++) {
          fbob[first_char][temp_bits] = bin;
          bin += nbob[first_char][temp_bits];
        }
        bin = 0;
        for (code_length = 1 ; code_length < max_code_length ; code_length++)
          while (bin < fbob[first_char][code_length+1])
            lookup_bits[first_char][bin++] = code_length;
        while (bin < 0x1000)
          lookup_bits[first_char][bin++] = max_code_length;
      }
    }
  }
  return;
}


void remove_dictionary_symbol(uint32_t symbol, uint8_t bits) {
  uint8_t first_char = symbol_strings[symbol_data[symbol].string_index];
  if (UTF8_compliant && (first_char > 0x80))
    first_char = 0x80;
  uint32_t list_length = --nsob[first_char][bits];
  uint32_t last_symbol = sym_list_ptrs[first_char][bits][list_length];
  sym_list_ptrs[first_char][bits][symbol_data[symbol].dictionary_index] = last_symbol;
  symbol_data[last_symbol].dictionary_index = symbol_data[symbol].dictionary_index;
  return;
}


void insert_mtf_queue(uint8_t cap_type) {
  remove_dictionary_symbol(symbol_number,CodeLength);
  if (--symbol_data[symbol_number].remaining) {
    symbol_count = symbol_data[symbol_number].instances;
    mtf_queue_number = symbol_count - 2;
    UpFreqMtfQueueNum(cap_type);
    if (mtf_queue_size[symbol_count] != MTF_QUEUE_SIZE)
      mtf_queue[symbol_count][((mtf_queue_offset[symbol_count] + mtf_queue_size[symbol_count]++) & 0x3F)] = symbol_number;
    else {
      mtf_queue_ptr = &mtf_queue[symbol_count][mtf_queue_offset[symbol_count]++ & 0x3F];
      add_dictionary_symbol(*mtf_queue_ptr,CodeLength);
      *mtf_queue_ptr = symbol_number;
    }
  }
  else {
    check_free_symbol();
  }
  return;
}


#define get_long_symbol() { \
  uint8_t index_bits = CodeLength - bin_code_length[FirstChar]; \
  uint32_t msib = nbob[FirstChar][CodeLength] << index_bits; \
  uint32_t shifted_max_symbols = msib >> 1; \
  uint32_t * sym_list_ptr = sym_list_ptrs[FirstChar][CodeLength]; \
  if (shifted_max_symbols >= nsob[FirstChar][CodeLength]) { \
    uint8_t reduce_bits = 1; \
    while ((shifted_max_symbols >>= 1) >= nsob[FirstChar][CodeLength]) \
      reduce_bits++; \
    if (index_bits <= reduce_bits) { \
      SymbolIndex = BinNum - fbob[FirstChar][CodeLength]; \
      uint32_t extra_code_bins = 0; \
      if (SymbolIndex) { \
        int32_t index = SymbolIndex; \
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


void get_short_symbol() {
  uint32_t extra_code_bins = 0;
  uint32_t index = (BinNum - fbob[FirstChar][CodeLength]) >> (bin_code_length[FirstChar] - CodeLength);
  uint32_t temp_index = index;
  if (temp_index && (symbol_data[sym_list_ptrs[FirstChar][CodeLength][--temp_index]].type & 8)) {
    extra_code_bins++;
    while (temp_index && (symbol_data[sym_list_ptrs[FirstChar][CodeLength][--temp_index]].type & 8))
      extra_code_bins++;
    low -= range * extra_code_bins;
    while (symbol_data[sym_list_ptrs[FirstChar][CodeLength][index]].type & 8) {
      index++;
      extra_code_bins++;
    }
    range *= 1 + extra_code_bins;
  }
  else if (symbol_data[sym_list_ptrs[FirstChar][CodeLength][index]].type & 8) {
    extra_code_bins++;
    while (symbol_data[sym_list_ptrs[FirstChar][CodeLength][++index]].type & 8)
      extra_code_bins++;
    range *= 1 + extra_code_bins;
  }
  symbol_number = sym_list_ptrs[FirstChar][CodeLength][index];
  return;
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
      uint8_t mtf_queue_last_position = (mtf_queue_offset[2] + --mtf_queue_size[2]) & 0x3F;
      uint8_t mtf_queue_position = (mtf_queue_last_position - Symbol) & 0x3F;
      symbol_number = *((mtf_queue_ptr = &mtf_queue[2][0]) + mtf_queue_position);
      do { // move the newer symbols up
        *(mtf_queue_ptr + mtf_queue_position) = *(mtf_queue_ptr + ((mtf_queue_position + 1) & 0x3F));
      } while ((mtf_queue_position = (mtf_queue_position + 1) & 0x3F) != mtf_queue_last_position);
    }
    check_free_symbol();
  }
  else {
    DecodeMtfQueueNumFinish(NOT_CAP);
    DecodeMtfQueuePosStart(NOT_CAP, mtf_queue_number);
    if (DecodeMtfQueuePosCheck0(NOT_CAP, mtf_queue_number)) {
      DecodeMtfQueuePosFinish0(NOT_CAP, mtf_queue_number);
      mtf_queue_number += 2;
      symbol_number
          = mtf_queue[mtf_queue_number][(mtf_queue_offset[mtf_queue_number] + mtf_queue_size[mtf_queue_number] - 1) & 0x3F];
      // decrement the mtf queue size if this is the last instance of this symbol
      if (--symbol_data[symbol_number].remaining) {
        mtf_queue_number -= 2;
        UpFreqMtfQueueNum(NOT_CAP);
      }
      else {
        mtf_queue_size[mtf_queue_number]--;
        check_free_symbol();
      }
    }
    else {
      DecodeMtfQueuePosFinish(NOT_CAP, mtf_queue_number);
      mtf_queue_number += 2;
      uint8_t mtf_queue_last_position = (mtf_queue_offset[mtf_queue_number] + mtf_queue_size[mtf_queue_number] - 1) & 0x3F;
      uint8_t mtf_queue_position = (mtf_queue_last_position - Symbol) & 0x3F;
      // remove this symbol from its current mtf queue position
      symbol_number = *((mtf_queue_ptr = &mtf_queue[mtf_queue_number][0]) + mtf_queue_position);
      do { // move the newer symbols up
        *(mtf_queue_ptr + mtf_queue_position) = *(mtf_queue_ptr + ((mtf_queue_position + 1) & 0x3F));
        mtf_queue_position = (mtf_queue_position + 1) & 0x3F;
      } while (mtf_queue_position != mtf_queue_last_position);
      if (--symbol_data[symbol_number].remaining) { // put symbol on top of mtf queue
        *(mtf_queue_ptr + mtf_queue_position) = symbol_number;
        mtf_queue_number -= 2;
        UpFreqMtfQueueNum(NOT_CAP);
      }
      else { // last instance - decrement the mtf queue size
        mtf_queue_size[mtf_queue_number]--;
        check_free_symbol();
      }
    }
  }
  return;
}


void get_mtf_symbol_cap() {
  DecodeMtfQueueNumStart(CAP);
  if (DecodeMtfQueueNumCheck0(CAP)) {
    DecodeMtfQueueNumFinish0(CAP);
    DecodeMtfQueuePosStart(CAP, 0);
    if (DecodeMtfQueuePosCheck0(CAP, 0)) {
      DecodeMtfQueuePosFinish0(CAP, 0);
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
      uint8_t num_az = Symbol + 1;
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
    check_free_symbol();
  }
  else {
    DecodeMtfQueueNumFinish(CAP);
    DecodeMtfQueuePosStart(CAP, mtf_queue_number);
    if (DecodeMtfQueuePosCheck0(CAP, mtf_queue_number)) {
      DecodeMtfQueuePosFinish0(CAP, mtf_queue_number);
      mtf_queue_number += 2;
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
      uint8_t num_az = Symbol + 1;
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
      UpFreqMtfQueueNum(CAP);
    }
    else { // last instance - decrement the mtf queue size
      mtf_queue_size[mtf_queue_number]--;
      check_free_symbol();
    }
  }
  return;
}


uint32_t get_extra_length() {
  uint8_t temp_bits, data_bits = 0;
  uint32_t SymsInDef;
  DecodeExtraLength();
  while (Symbol == 3) {
    data_bits += 2;
    DecodeExtraLength();
  }
  if (Symbol == 2) {
    data_bits += 2;
    temp_bits = data_bits;
    SymsInDef = 0;
  }
  else {
    temp_bits = data_bits++;
    SymsInDef = Symbol;
  }
  while (temp_bits) {
    temp_bits -= 2;
    DecodeExtraLength();
    SymsInDef = (SymsInDef << 2) + Symbol;
  }
  return(SymsInDef + (1 << data_bits) + 14);
}


#define copy_string(in, len, out) { \
  while (len >= 8) { \
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
    len -= 8; \
  } \
  while (len--) \
    *out++ = *in++; \
}


void check_free_strings(uint32_t define_string_index, uint32_t string_length) {
  if (no_embed && free_string_list_length) {
    uint8_t free_string_list_index = free_string_list_length - 1;
    do {
      if ((free_string_list[free_string_list_index].wait_cycles == 0)
          && (free_string_list[free_string_list_index].string_length >= string_length)) {
        symbol_data[symbol_number].string_index = free_string_list[free_string_list_index].string_index;
        symbol_data[num_symbols_defined].string_index = define_string_index;
        uint8_t * define_string_ptr = &symbol_strings[define_string_index];
        uint8_t * free_string_ptr = &symbol_strings[free_string_list[free_string_list_index].string_index];
        free_string_list[free_string_list_index].string_index += string_length;
        free_string_list[free_string_list_index].string_length -= string_length;
        if (free_string_list[free_string_list_index].string_length <= 2)
          free_string_list_length--;
        copy_string(define_string_ptr, string_length, free_string_ptr);
        if ((free_string_list_index < 0x1F)
            && (free_string_list[free_string_list_index+1].string_length
              > free_string_list[free_string_list_index].string_length)) {
          uint32_t temp_string_index = free_string_list[free_string_list_index].string_index;
          uint32_t temp_string_length = free_string_list[free_string_list_index].string_length;
          uint8_t temp_wait_cycles = free_string_list[free_string_list_index].wait_cycles;
          free_string_list[free_string_list_index].string_index = free_string_list[free_string_list_index+1].string_index;
          free_string_list[free_string_list_index].string_length = free_string_list[free_string_list_index+1].string_length;
          free_string_list[free_string_list_index].wait_cycles = free_string_list[free_string_list_index+1].wait_cycles;
          free_string_list_index++;
          while ((free_string_list_index < 0x1F)
              && (free_string_list[free_string_list_index+1].string_length > temp_string_length)) {
            free_string_list[free_string_list_index].string_index = free_string_list[free_string_list_index+1].string_index;
            free_string_list[free_string_list_index].string_length = free_string_list[free_string_list_index+1].string_length;
            free_string_list[free_string_list_index].wait_cycles = free_string_list[free_string_list_index+1].wait_cycles;
            free_string_list_index++;
          }
          free_string_list[free_string_list_index].string_index = temp_string_index;
          free_string_list[free_string_list_index].string_length = temp_string_length;
          free_string_list[free_string_list_index].wait_cycles = temp_wait_cycles;
        }
        break;
      }
    } while (free_string_list_index--);
  }
  return;
}


void create_EOF_symbol() {
  find_first_symbol = 0;
  if (UTF8_compliant && (base_symbol > 0x80))
    end_symbol = 0x80;
  else
    end_symbol = base_symbol;
  sym_list_ptrs[end_symbol][max_code_length][0] = MAX_SYMBOLS_DEFINED - 1;
  nsob[end_symbol][max_code_length] = 1;
  if (max_code_length >= 12) {
    bin_code_length[end_symbol] = max_code_length;
    sum_nbob[end_symbol] = nbob[end_symbol][max_code_length] = 1;
  }
  else
    sum_nbob[end_symbol] = nbob[end_symbol][max_code_length] = 1 << (12 - max_code_length);
  return;
}


void write_extended_UTF8_symbol(uint32_t * index_ptr) {
  if (base_symbol < START_UTF8_3BYTE_symbols) {
    symbol_strings[(*index_ptr)++] = (uint8_t)(base_symbol >> 6) + 0xC0;
    symbol_strings[(*index_ptr)++] = (uint8_t)(base_symbol & 0x3F) + 0x80;
  }
  else if (base_symbol < START_UTF8_4BYTE_symbols) {
    symbol_strings[(*index_ptr)++] = (uint8_t)(base_symbol >> 12) + 0xE0;
    symbol_strings[(*index_ptr)++] = (uint8_t)((base_symbol >> 6) & 0x3F) + 0x80;
    symbol_strings[(*index_ptr)++] = (uint8_t)(base_symbol & 0x3F) + 0x80;
  }
  else {
    symbol_strings[(*index_ptr)++] = (uint8_t)(base_symbol >> 18) + 0xF0;
    symbol_strings[(*index_ptr)++] = (uint8_t)((base_symbol >> 12) & 0x3F) + 0x80;
    symbol_strings[(*index_ptr)++] = (uint8_t)((base_symbol >> 6) & 0x3F) + 0x80;
    symbol_strings[(*index_ptr)++] = (uint8_t)(base_symbol & 0x3F) + 0x80;
  }
  return;
}


void delta_transform(uint8_t * buffer, uint32_t len) {
  uint8_t * char_ptr = buffer;
  if (delta_on == 0) {
    if (len > stride) {
      if (stride > 4) {
        char_ptr = buffer + 1;
        do {
          *char_ptr += *(char_ptr - 1);
        } while (++char_ptr < buffer + stride);
      }
      delta_on = 1;
      char_ptr = buffer + stride;
      len -= stride;
    }
    else {
      if (stride > 4) {
        char_ptr = buffer + 1;
        do {
          *char_ptr += *(char_ptr - 1);
        } while (++char_ptr < buffer + len);
      }
      else
        char_ptr = buffer + len;
      len = 0;
    }
  }
  if (stride == 1) {
    while (len--) {
      *char_ptr += *(char_ptr - 1);
      char_ptr++;
    }
  }
  else if (stride == 2) {
    while (len--) {
      if ((delta_format & 4) == 0) {
        *char_ptr += *(char_ptr - 2);
        char_ptr++;
      }
      else {
        char_ptr++;
        if (((char_ptr - buffer) & 1) == 0) {
          if ((delta_format & 8) == 0) {
            uint32_t value = (*(char_ptr - 4) << 8) + *(char_ptr - 3) + (*(char_ptr - 2) << 8) + *(char_ptr - 1) - 0x80;
            *(char_ptr - 2) = (value >> 8) & 0xFF;
            *(char_ptr - 1) = value & 0xFF;
          }
          else {
            uint32_t value = (*(char_ptr - 3) << 8) + *(char_ptr - 4) + (*(char_ptr - 1) << 8) + *(char_ptr - 2) - 0x80;
            *(char_ptr - 1) = (value >> 8) & 0xFF;
            *(char_ptr - 2) = value & 0xFF;
          }
        }
      }
    }
  }
  else if (stride == 3) {
    while (len--) {
      *char_ptr += *(char_ptr - 3);
      char_ptr++;
    }
  }
  else if (stride == 4) {
    while (len--) {
      char_ptr++;
      if ((delta_format & 4) == 0) {
        *(char_ptr - 1) += *(char_ptr - 5);
      }
      else if ((delta_format & 0x10) != 0) {
        if (((char_ptr - buffer) & 1) == 0) {
          if ((delta_format & 8) == 0) {
            uint32_t value = (*(char_ptr - 6) << 8) + *(char_ptr - 5) + (*(char_ptr - 2) << 8) + *(char_ptr - 1) - 0x80;
            *(char_ptr - 2) = (value >> 8) & 0xFF;
            *(char_ptr - 1) = value & 0xFF;
          }
          else {
            uint32_t value = (*(char_ptr - 5) << 8) + *(char_ptr - 6) + (*(char_ptr - 1) << 8) + *(char_ptr - 2) - 0x80;
            *(char_ptr - 1) = (value >> 8) & 0xFF;
            *(char_ptr - 2) = value & 0xFF;
          }
        }
      }
      else {
        if (((char_ptr - buffer) & 3) == 0) {
          if ((delta_format & 8) == 0) {
            uint32_t value = (*(char_ptr - 8) << 24) + (*(char_ptr - 7) << 16) + (*(char_ptr - 6) << 8) + *(char_ptr - 5)
                + (*(char_ptr - 4) << 24) + (*(char_ptr - 3) << 16) + (*(char_ptr - 2) << 8) + *(char_ptr - 1) - 0x808080;
            *(char_ptr - 4) = value >> 24;
            *(char_ptr - 3) = (value >> 16) & 0xFF;
            *(char_ptr - 2) = (value >> 8) & 0xFF;
            *(char_ptr - 1) = value & 0xFF;
          }
          else {
            uint32_t value = (*(char_ptr - 5) << 24) + (*(char_ptr - 6) << 16) + (*(char_ptr - 7) << 8) + *(char_ptr - 8)
                + (*(char_ptr - 1) << 24) + (*(char_ptr - 2) << 16) + (*(char_ptr - 3) << 8) + *(char_ptr - 4) - 0x808080;
            *(char_ptr - 1) = value >> 24;
            *(char_ptr - 2) = (value >> 16) & 0xFF;
            *(char_ptr - 3) = (value >> 8) & 0xFF;
            *(char_ptr - 4) = value & 0xFF;
          }
        }
      }
    }
  }
  else {
    while (len--) {
      *char_ptr += *(char_ptr - stride);
      char_ptr++;
    }
  }
}


void increase_dictionary_size() {
  dictionary_size <<= 1;
  if (two_threads != 0) {
    if (symbol_buffer_write_index < 0x100)
      while (atomic_load_explicit(&symbol_buffer_pt2_owner, memory_order_acquire) != 0);
    else
      while (atomic_load_explicit(&symbol_buffer_pt1_owner, memory_order_acquire) != 0);
  }
  if ((symbol_strings = (uint8_t *)realloc(symbol_strings, dictionary_size)) == 0) {
    fprintf(stderr,"FATAL ERROR - dictionary realloc failure\n");
    exit(EXIT_FAILURE);
  }
}


uint32_t decode_define(uint32_t define_string_index) {
  uint8_t define_symbol_instances, new_symbol_code_length;
  uint32_t symbols_in_definition, end_define_string_index;

  end_define_string_index = define_string_index;
  DecodeSIDStart(NOT_CAP);
  if (DecodeSIDCheck0(NOT_CAP)) {
    DecodeSIDFinish0(NOT_CAP);
    DecodeINSTStart(NOT_CAP);
    if (DecodeINSTCheck0(NOT_CAP)) {
      DecodeINSTFinish0(NOT_CAP);
      define_symbol_instances = 2;
      new_symbol_code_length = max_code_length;
    }
    else {
      DecodeINSTFinish(NOT_CAP);
      if (Instances >= MAX_INSTANCES_FOR_MTF_QUEUE) {
        define_symbol_instances = 0;
        new_symbol_code_length = max_regular_code_length + MAX_INSTANCES_FOR_MTF_QUEUE - Instances;
      }
      else if (Instances != MAX_INSTANCES_FOR_MTF_QUEUE - 1) {
        define_symbol_instances = Instances + 2;
        new_symbol_code_length = mtf_queue_miss_code_length[define_symbol_instances];
      }
      else {
        define_symbol_instances = 1;
        new_symbol_code_length = 0x20;
      }
    }

    DecodeBaseSymbol(base_symbol, base_bits, num_base_symbols);
    if (end_define_string_index + 4 >= dictionary_size)
      increase_dictionary_size();
    if ((UTF8_compliant == 0) || (base_symbol < 0x80)) {
      if (symbol_lengths[base_symbol]) {
        if (base_symbol & 1) {
          base_symbol -= 1;
          low -= range;
          range <<= 1;
        }
        else {
          base_symbol += 1;
          range <<= 1;
        }
      }
      else if (base_symbol & 1) {
        if (symbol_lengths[base_symbol - 1]) {
          low -= range;
          range <<= 1;
        }
      }
      else if (symbol_lengths[base_symbol + 1])
        range <<= 1;
    }

    symbol_number = (free_symbol_list_length == 0) ? num_symbols_defined : free_symbol_list[--free_symbol_list_length];
    if (UTF8_compliant) {
      if (base_symbol < 0x80) {
        symbol_lengths[base_symbol] = new_symbol_code_length;
        uint8_t j1 = 0x80;
        do {
          InitFirstCharBin(j1, (uint8_t)base_symbol, new_symbol_code_length);
        } while (j1--);
        j1 = 0x80;
        do {
          InitSymbolFirstChar(base_symbol, j1);
          if (symbol_lengths[j1])
            InitTrailingCharBin((uint8_t)base_symbol, j1, symbol_lengths[j1]);
        } while (j1--);
      }
      else if (symbol_lengths[0x80] == 0) {
        symbol_lengths[0x80] = new_symbol_code_length;
        uint8_t j1 = 0x7F;
        do {
          InitFirstCharBin(j1, 0x80, new_symbol_code_length);
        } while (j1--);
        j1 = 0x80;
        do {
          InitSymbolFirstChar(0x80, j1);
          if (symbol_lengths[j1])
            InitTrailingCharBin(0x80, j1, symbol_lengths[j1]);
        } while (j1--);
        InitFreqFirstChar(0x80, 0x80);
      }
      if (base_symbol < START_UTF8_2BYTE_symbols)
        symbol_strings[end_define_string_index++] = symbol_data[symbol_number].ends = prior_end = (uint8_t)base_symbol;
      else {
        symbol_data[symbol_number].ends = prior_end = 0x80;
        write_extended_UTF8_symbol(&end_define_string_index);
      }
    }
    else {
      symbol_lengths[base_symbol] = new_symbol_code_length;
      uint8_t j1 = 0xFF;
      do {
        InitFirstCharBinBinary(j1, (uint8_t)base_symbol, new_symbol_code_length);
      } while (j1--);
      InitTrailingCharBinary(base_symbol);
      symbol_strings[end_define_string_index++] = symbol_data[symbol_number].ends = prior_end = (uint8_t)base_symbol;
    }

    if (find_first_symbol) {
      create_EOF_symbol();
    }
    if (define_symbol_instances == 1) {
      symbol_data[symbol_number].string_index = define_string_index;
      symbol_data[symbol_number].string_length = end_define_string_index - define_string_index;
      symbol_data[symbol_number].type &= 0xFE;
      if (symbol_number == num_symbols_defined)
        num_symbols_defined++;
      symbol_data[num_symbols_defined].string_index = end_define_string_index;
      return(end_define_string_index);
    }
  }
  else {
    DecodeSIDFinish(NOT_CAP);
    symbols_in_definition = SIDSymbol + 1;
    if (symbols_in_definition == 16) {
      symbols_in_definition = get_extra_length();
    }
    DecodeINSTStart(NOT_CAP);
    if (DecodeINSTCheck0(NOT_CAP)) {
      DecodeINSTFinish0(NOT_CAP);
      define_symbol_instances = 2;
      new_symbol_code_length = max_code_length;
    }
    else {
      DecodeINSTFinish(NOT_CAP);
      if (Instances >= MAX_INSTANCES_FOR_MTF_QUEUE) {
        define_symbol_instances = 0;
        new_symbol_code_length = max_regular_code_length + MAX_INSTANCES_FOR_MTF_QUEUE - Instances;
      }
      else {
        define_symbol_instances = Instances + 2;
        new_symbol_code_length = mtf_queue_miss_code_length[define_symbol_instances];
      }
    }

    do { // Build the symbol string from the next symbols_in_definition symbols
      DecodeSymTypeStart(LEVEL1);
      if (DecodeSymTypeCheckDict(LEVEL1)) {
        DecodeSymTypeFinishDict(LEVEL1);
        if (UTF8_compliant) {
          DecodeFirstChar(0, prior_end);
        }
        else {
          DecodeFirstCharBinary(prior_end);
        }
        DictionaryBins = sum_nbob[FirstChar];
        DecodeDictionaryBin(lookup_bits[FirstChar]);
        if (CodeLength > bin_code_length[FirstChar]) {
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
            check_free_symbol();
          }
        }
        else if (symbol_data[symbol_number].type & 4) {
          add_new_symbol_to_mtfg_queue(symbol_number);
        }
        prior_end = symbol_data[symbol_number].ends;
        uint32_t string_length = symbol_data[symbol_number].string_length;
        if (end_define_string_index + string_length >= dictionary_size)
          increase_dictionary_size();
        uint8_t * symbol_string_ptr = &symbol_strings[symbol_data[symbol_number].string_index];
        while (string_length--)
          symbol_strings[end_define_string_index++] = *symbol_string_ptr++;
      }
      else if (DecodeSymTypeCheckNew(LEVEL1)) {
        DecodeSymTypeFinishNew(LEVEL1);
        no_embed = 0;
        end_define_string_index = decode_define(end_define_string_index);
      }
      else {
        if (DecodeSymTypeCheckMtfg(LEVEL1)) {
          DecodeSymTypeFinishMtfg(LEVEL1);
          get_mtfg_symbol();
        }
        else {
          DecodeSymTypeFinishMtf(LEVEL1);
          get_mtf_symbol();
        }
        prior_end = symbol_data[symbol_number].ends;
        uint32_t string_length = symbol_data[symbol_number].string_length;
        if (end_define_string_index + string_length >= dictionary_size)
          increase_dictionary_size();
        uint8_t * symbol_string_ptr = &symbol_strings[symbol_data[symbol_number].string_index];
        while (string_length--)
          symbol_strings[end_define_string_index++] = *symbol_string_ptr++;
      }
    } while (--symbols_in_definition);
    symbol_number = (free_symbol_list_length == 0) ? num_symbols_defined : free_symbol_list[--free_symbol_list_length];
    symbol_data[symbol_number].ends = prior_end;
  }

  uint32_t string_length = end_define_string_index - define_string_index;
  symbol_data[symbol_number].string_length = string_length;
  symbol_data[symbol_number].type |= no_embed;
  symbol_data[symbol_number].string_index = define_string_index;

  if (define_symbol_instances) { // mtf queue symbol
    symbol_data[symbol_number].instances = define_symbol_instances;
    symbol_data[symbol_number].remaining = define_symbol_instances - 1;
    if (use_mtf) {
      mtf_queue_number = define_symbol_instances - 2;
      UpFreqMtfQueueNum(NOT_CAP);
      if (mtf_queue_size[define_symbol_instances] != MTF_QUEUE_SIZE) // put the symbol in the mtf queue
        mtf_queue[define_symbol_instances]
              [(mtf_queue_size[define_symbol_instances]++ + mtf_queue_offset[define_symbol_instances]) & 0x3F] = symbol_number;
      else { // put last mtf queue symbol in symbol list
        uint32_t temp_symbol_number
            = *(mtf_queue_ptr = &mtf_queue[define_symbol_instances][mtf_queue_offset[define_symbol_instances]++ & 0x3F]);
        add_dictionary_symbol(temp_symbol_number,new_symbol_code_length);
        // put symbol in queue and rotate cyclical buffer
        *mtf_queue_ptr = symbol_number;
      }
    }
    else {
      add_dictionary_symbol(symbol_number,new_symbol_code_length);
    }
  }
  else { // put symbol in table
    if ((new_symbol_code_length > 10) && use_mtfg) {
      uint8_t nonergodic;
      DecodeERG(0);
      if (nonergodic) {
        symbol_data[symbol_number].type = 4;
        add_new_symbol_to_mtfg_queue(symbol_number);
      }
    }
    symbol_data[symbol_number].instances = MAX_INSTANCES_FOR_MTF_QUEUE + new_symbol_code_length;
    add_dictionary_symbol(symbol_number,new_symbol_code_length);
  }
  if (symbol_number == num_symbols_defined)
    num_symbols_defined++;
  symbol_data[num_symbols_defined].string_index = end_define_string_index;
  check_free_strings(define_string_index, string_length);
  return(end_define_string_index);
}


uint32_t decode_define_cap_encoded(uint32_t define_string_index) {
  uint32_t symbols_in_definition, end_define_string_index;
  uint8_t define_symbol_instances, new_symbol_code_length, char_before_define_is_cap;
  uint8_t tag_type = 0;

  char_before_define_is_cap = prior_is_cap;
  end_define_string_index = define_string_index;

  DecodeSIDStart(prior_is_cap);
  if (DecodeSIDCheck0(prior_is_cap)) {
    DecodeSIDFinish0(prior_is_cap);
    DecodeINSTStart(prior_is_cap);
    if (DecodeINSTCheck0(prior_is_cap)) {
      DecodeINSTFinish0(prior_is_cap);
      define_symbol_instances = 2;
      new_symbol_code_length = max_code_length;
    }
    else {
      DecodeINSTFinish(prior_is_cap);
      if (Instances >= MAX_INSTANCES_FOR_MTF_QUEUE) {
        define_symbol_instances = 0;
        new_symbol_code_length = max_regular_code_length + MAX_INSTANCES_FOR_MTF_QUEUE - Instances;
      }
      else if (Instances != MAX_INSTANCES_FOR_MTF_QUEUE - 1) {
        define_symbol_instances = Instances + 2;
        new_symbol_code_length = mtf_queue_miss_code_length[define_symbol_instances];
      }
      else {
        define_symbol_instances = 1;
        new_symbol_code_length = 0x20;
      }
    }

    DecodeBaseSymbol(base_symbol, base_bits, num_base_symbols);
    if (base_symbol > 0x42)
      base_symbol += 24;
    else if (base_symbol > 0x40)
      base_symbol += 1;
    if (end_define_string_index + 4 >= dictionary_size)
      increase_dictionary_size();
    if ((UTF8_compliant == 0) || (base_symbol < 0x80)) {
      if (symbol_lengths[base_symbol]) {
        if (base_symbol & 1) {
          base_symbol -= 1;
          low -= range;
          range <<= 1;
        }
        else {
          base_symbol += 1;
          range <<= 1;
        }
      }
      else if (base_symbol & 1) {
        if (symbol_lengths[base_symbol - 1]) {
          low -= range;
          range <<= 1;
        }
      }
      else if (symbol_lengths[base_symbol + 1])
        range <<= 1;
      symbol_lengths[base_symbol] = new_symbol_code_length;
      if (UTF8_compliant) {
        InitBaseSymbolCap(base_symbol, 0x80, new_symbol_code_length);
      }
      else {
        InitBaseSymbolCap(base_symbol, 0xFF, new_symbol_code_length);
      }
    }
    else if (symbol_lengths[0x80] == 0) {
      symbol_lengths[0x80] = new_symbol_code_length;
      uint8_t j1 = 0x7F;
      do {
        InitFirstCharBin(j1, 0x80, new_symbol_code_length);
      } while (--j1 != 'Z');
      j1 = 'A' - 1;
      do {
        InitFirstCharBin(j1, 0x80, new_symbol_code_length);
      } while (j1--);
      j1 = 0x80;
      do {
        InitSymbolFirstChar(0x80, j1);
        if (symbol_lengths[j1])
          InitTrailingCharBin(0x80, j1, symbol_lengths[j1]);
        else if ((j1 == 'C') && cap_symbol_defined)
          InitTrailingCharBin(0x80, 'C', symbol_lengths[j1]);
        else if ((j1 == 'B') && cap_lock_symbol_defined)
          InitTrailingCharBin(0x80, 'B', symbol_lengths[j1]);
      } while (j1--);
    }

    symbol_number = (free_symbol_list_length == 0) ? num_symbols_defined : free_symbol_list[--free_symbol_list_length];
    if (base_symbol < START_UTF8_2BYTE_symbols) {
      symbol_strings[end_define_string_index++] = symbol_data[symbol_number].ends = prior_end = (uint8_t)base_symbol;
      if (base_symbol == 'C') {
        symbol_data[symbol_number].type = 0x10;
        prior_is_cap = 1;
      }
      else if (base_symbol == 'B') {
        symbol_data[symbol_number].type = 0x10;
        prior_is_cap = 1;
        symbol_data[symbol_number].ends = prior_end = 'C';
      }
      else {
        prior_is_cap = 0;
        if (base_symbol == ' ')
          symbol_data[symbol_number].type = 0x10;
        else if ((base_symbol >= 0x61) && (base_symbol <= 0x7A))
          symbol_data[symbol_number].type = 2;
        else
          symbol_data[symbol_number].type = 0;
      }
      symbol_data[symbol_number].string_length = 1;
    }
    else {
      symbol_data[symbol_number].type = 0;
      prior_is_cap = 0;
      if (UTF8_compliant) {
        symbol_data[symbol_number].ends = prior_end = 0x80;
        write_extended_UTF8_symbol(&end_define_string_index);
        symbol_data[symbol_number].string_length = end_define_string_index - define_string_index;
      }
      else {
        symbol_strings[end_define_string_index++] = symbol_data[symbol_number].ends = prior_end = (uint8_t)base_symbol;
        symbol_data[symbol_number].string_length = 1;
      }
    }
    if (find_first_symbol) {
      create_EOF_symbol();
    }
    symbol_data[symbol_number].type &= 0xFE;
    if (define_symbol_instances == 1) {
      symbol_data[symbol_number].string_index = define_string_index;
      if (symbol_number == num_symbols_defined)
        num_symbols_defined++;
      symbol_data[num_symbols_defined].string_index = end_define_string_index;
      return(end_define_string_index);
    }
  }
  else {
    DecodeSIDFinish(prior_is_cap);
    if ((symbols_in_definition = SIDSymbol + 1) == 16) {
      symbols_in_definition = get_extra_length();
    }
    DecodeINSTStart(prior_is_cap);
    if (DecodeINSTCheck0(prior_is_cap)) {
      DecodeINSTFinish0(prior_is_cap);
      define_symbol_instances = 2;
      new_symbol_code_length = max_code_length;
    }
    else {
      DecodeINSTFinish(prior_is_cap);
      if (Instances >= MAX_INSTANCES_FOR_MTF_QUEUE) {
        define_symbol_instances = 0;
        new_symbol_code_length = max_regular_code_length + MAX_INSTANCES_FOR_MTF_QUEUE - Instances;
      }
      else {
        define_symbol_instances = Instances + 2;
        new_symbol_code_length = mtf_queue_miss_code_length[define_symbol_instances];
      }
    }

    do { // Build the symbol string from the next symbols_in_definition symbols
      if (prior_is_cap == 0) {
        DecodeSymTypeStart(LEVEL1);
        if (DecodeSymTypeCheckDict(LEVEL1)) {
          DecodeSymTypeFinishDict(LEVEL1);
          if (prior_end != 0xA) {
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
          }
          else
            FirstChar = 0x20;
          DictionaryBins = sum_nbob[FirstChar];
          DecodeDictionaryBin(lookup_bits[FirstChar]);
          if (CodeLength > bin_code_length[FirstChar]) {
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
              check_free_symbol();
            }
          }
          else if (symbol_data[symbol_number].type & 4) {
            add_new_symbol_to_mtfg_queue(symbol_number);
          }
          prior_end = symbol_data[symbol_number].ends;
          prior_is_cap = (prior_end == 'C');
          uint32_t string_length = symbol_data[symbol_number].string_length;
          if (end_define_string_index + string_length >= dictionary_size)
            increase_dictionary_size();
          symbol_string_ptr = &symbol_strings[symbol_data[symbol_number].string_index];
          uint8_t * string_ptr = &symbol_strings[end_define_string_index];
          end_define_string_index += string_length;
          uint8_t * end_string_ptr = &symbol_strings[end_define_string_index];
          while (string_ptr != end_string_ptr)
            *string_ptr++ = *symbol_string_ptr++;
        }
        else if (DecodeSymTypeCheckNew(LEVEL1)) {
          DecodeSymTypeFinishNew(LEVEL1);
          no_embed = 0;
          end_define_string_index = decode_define_cap_encoded(end_define_string_index);
        }
        else {
          if (DecodeSymTypeCheckMtfg(LEVEL1)) {
            DecodeSymTypeFinishMtfg(LEVEL1);
            get_mtfg_symbol();
          }
          else {
            DecodeSymTypeFinishMtf(LEVEL1);
            get_mtf_symbol();
          }
          prior_end = symbol_data[symbol_number].ends;
          prior_is_cap = (prior_end == 'C');
          uint32_t string_length = symbol_data[symbol_number].string_length;
          if (end_define_string_index + string_length >= dictionary_size)
            increase_dictionary_size();
          symbol_string_ptr = &symbol_strings[symbol_data[symbol_number].string_index];
          uint8_t * string_ptr = &symbol_strings[end_define_string_index];
          end_define_string_index += string_length;
          uint8_t * end_string_ptr = &symbol_strings[end_define_string_index];
          while (string_ptr != end_string_ptr)
            *string_ptr++ = *symbol_string_ptr++;
        }
      }
      else { // prior_is_cap
        DecodeSymTypeStart(LEVEL1_CAP);
        if (DecodeSymTypeCheckDict(LEVEL1_CAP)) {
          DecodeSymTypeFinishDict(LEVEL1_CAP);
          DecodeFirstChar(0, 'C');
          DictionaryBins = sum_nbob[FirstChar];
          DecodeDictionaryBin(lookup_bits[FirstChar]);
          if (CodeLength > bin_code_length[FirstChar]) {
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
              check_free_symbol();
            }
          }
          else if (symbol_data[symbol_number].type & 4) {
            add_new_symbol_to_mtfg_queue(symbol_number);
          }
          prior_end = symbol_data[symbol_number].ends;
          prior_is_cap = (prior_end == 'C');
          uint32_t string_length = symbol_data[symbol_number].string_length;
          if (end_define_string_index + string_length >= dictionary_size)
            increase_dictionary_size();
          symbol_string_ptr = &symbol_strings[symbol_data[symbol_number].string_index];
          uint8_t * string_ptr = &symbol_strings[end_define_string_index];
          end_define_string_index += string_length;
          uint8_t * end_string_ptr = &symbol_strings[end_define_string_index];
          while (string_ptr != end_string_ptr)
            *string_ptr++ = *symbol_string_ptr++;
        }
        else if (DecodeSymTypeCheckNew(LEVEL1_CAP)) {
          DecodeSymTypeFinishNew(LEVEL1_CAP);
          no_embed = 0;
          end_define_string_index = decode_define_cap_encoded(end_define_string_index);
        }
        else {
          if (DecodeSymTypeCheckMtfg(LEVEL1_CAP)) {
            DecodeSymTypeFinishMtfg(LEVEL1_CAP);
            get_mtfg_symbol_cap();
          }
          else {
            DecodeSymTypeFinishMtf(LEVEL1_CAP);
            get_mtf_symbol_cap();
          }
          prior_end = symbol_data[symbol_number].ends;
          prior_is_cap = (prior_end == 'C');
          uint32_t string_length = symbol_data[symbol_number].string_length;
          if (end_define_string_index + string_length >= dictionary_size)
            increase_dictionary_size();
          symbol_string_ptr = &symbol_strings[symbol_data[symbol_number].string_index];
          uint8_t * string_ptr = &symbol_strings[end_define_string_index];
          end_define_string_index += string_length;
          uint8_t * end_string_ptr = &symbol_strings[end_define_string_index];
          while (string_ptr != end_string_ptr)
            *string_ptr++ = *symbol_string_ptr++;
        }
      }
    } while (--symbols_in_definition);

    uint32_t subsymbol_number = symbol_number;
    symbol_number = (free_symbol_list_length == 0) ? num_symbols_defined : free_symbol_list[--free_symbol_list_length];
    symbol_data[symbol_number].ends = prior_end;
    uint32_t string_length = end_define_string_index - define_string_index;
    symbol_data[symbol_number].string_length = string_length;
    symbol_data[symbol_number].type = (((symbol_strings[define_string_index] >= 'a')
        && (symbol_strings[define_string_index] <= 'z')) << 1) | no_embed;

    if (max_code_length >= 14) {
      if (symbol_data[subsymbol_number].type & 0x10) {
        symbol_data[symbol_number].type |= symbol_data[subsymbol_number].type & 0x30;
        if (symbol_data[symbol_number].type & 0x20) {
          if (symbol_data[subsymbol_number].type & 0x80)
            symbol_data[symbol_number].type |= 0xC0;
          else if (define_symbol_instances == 0) {
            DecodeWordTag();
            tag_type = 1 + Symbol;
            symbol_data[symbol_number].type |= 0x40 + (Symbol << 7);
          }
          else
            symbol_data[symbol_number].type |= symbol_data[subsymbol_number].type & 0xC0;
        }
      }
      else {
        symbol_string_ptr = &symbol_strings[end_define_string_index];
        symbol_string_ptr--;
        if ((symbol_data[symbol_number].ends == 'C') || (*symbol_string_ptr == (uint32_t)' '))
          symbol_data[symbol_number].type |= 0x10;
        else {
          while (symbol_string_ptr-- != &symbol_strings[define_string_index]) {
            if (*symbol_string_ptr == (uint32_t)' ') {
              symbol_data[symbol_number].type |= 0x30;
              if (define_symbol_instances == 0) {
                DecodeWordTag();
                tag_type = 1 + Symbol;
                symbol_data[symbol_number].type |= 0x40 + (Symbol << 7);
              }
              break;
            }
          }
        }
      }
    }
  }

  uint32_t string_length = end_define_string_index - define_string_index;
  symbol_data[symbol_number].string_length = string_length;
  symbol_data[symbol_number].type |= no_embed;
  symbol_data[symbol_number].string_index = define_string_index;

  if (define_symbol_instances) {
    symbol_data[symbol_number].instances = define_symbol_instances;
    symbol_data[symbol_number].remaining = define_symbol_instances - 1;
    if (use_mtf) {
      mtf_queue_number = define_symbol_instances - 2;
      if (char_before_define_is_cap == 0) {
        UpFreqMtfQueueNum(NOT_CAP);
      }
      else {
        UpFreqMtfQueueNum(CAP);
      }
      if (mtf_queue_size[define_symbol_instances] != MTF_QUEUE_SIZE) // put the symbol in the mtf queue
        mtf_queue[define_symbol_instances]
              [(mtf_queue_size[define_symbol_instances]++ + mtf_queue_offset[define_symbol_instances]) & 0x3F]
            = symbol_number;
      else { // put last mtf queue symbol in symbol list
        uint32_t temp_symbol_number
            = *(mtf_queue_ptr = &mtf_queue[define_symbol_instances][mtf_queue_offset[define_symbol_instances]++ & 0x3F]);
        add_dictionary_symbol(temp_symbol_number,new_symbol_code_length);
        // put symbol in queue and rotate cyclical buffer
        *mtf_queue_ptr = symbol_number;
      }
    }
    else {
      add_dictionary_symbol(symbol_number,new_symbol_code_length);
    }
  }
  else { // put symbol in table
    if ((new_symbol_code_length > 10) && use_mtfg) {
      uint8_t nonergodic;
      DecodeERG(tag_type);
      if (nonergodic) {
        symbol_data[symbol_number].type |= 4;
        add_new_symbol_to_mtfg_queue(symbol_number);
      }
    }
    symbol_data[symbol_number].instances = MAX_INSTANCES_FOR_MTF_QUEUE + new_symbol_code_length;
    add_dictionary_symbol(symbol_number,new_symbol_code_length);
  }

  if (symbol_number == num_symbols_defined)
    num_symbols_defined++;
  symbol_data[num_symbols_defined].string_index = end_define_string_index;
  check_free_strings(define_string_index, string_length);
  return(end_define_string_index);
}


void transpose2(uint8_t * buffer, uint32_t len) {
  uint8_t *char_ptr, *char2_ptr;
  uint32_t block1_len = len - (len >> 1);
  char2_ptr = out_char2;
  char_ptr = buffer + block1_len;
  while (char_ptr < buffer + len)
    *char2_ptr++ = *char_ptr++;
  char2_ptr = buffer + 2 * block1_len;
  char_ptr = buffer + block1_len;
  while (char_ptr != buffer) {
    char2_ptr -= 2;
    *char2_ptr = *--char_ptr;
  }
  char2_ptr = buffer + 1;
  char_ptr = out_char2;
  while (char2_ptr < buffer + len) {
    *char2_ptr = *char_ptr++;
    char2_ptr += 2;
  }
  return;
}


void transpose4(uint8_t * buffer, uint32_t len) {
  uint8_t *char_ptr, *char2_ptr;
  uint32_t block1_len = (len + 3) >> 2;
  char2_ptr = out_char2;
  char_ptr = buffer + block1_len;
  while (char_ptr < buffer + len)
    *char2_ptr++ = *char_ptr++;
  char2_ptr = buffer + 4 * block1_len;
  char_ptr = buffer + block1_len;
  while (char_ptr != buffer) {
    char2_ptr -= 4;
    *char2_ptr = *--char_ptr;
  }
  char2_ptr = buffer + 1;
  char_ptr = out_char2;
  while (char2_ptr < buffer + len) {
    *char2_ptr = *char_ptr++;
    char2_ptr += 4;
  }
  char2_ptr = buffer + 2;
  while (char2_ptr < buffer + len) {
    *char2_ptr = *char_ptr++;
    char2_ptr += 4;
  }
  char2_ptr = buffer + 3;
  while (char2_ptr < buffer + len) {
    *char2_ptr = *char_ptr++;
    char2_ptr += 4;
  }
  return;
}


#define write_output_buffer() { \
  fflush(fd_out); \
  chars_to_write = out_char_ptr - start_char_ptr; \
  fwrite(start_char_ptr,1,chars_to_write,fd_out); \
  out_chars += chars_to_write; \
  if (out_buffer_num == 0) { \
    out_buffer_num = 1; \
    out_char_ptr = out_char1; \
    start_char_ptr = out_char_ptr; \
    extra_out_char_ptr = out_char_ptr + CHARS_TO_WRITE; \
  } \
  else { \
    out_buffer_num = 0; \
    out_char_ptr = out_char0; \
    start_char_ptr = out_char_ptr; \
    extra_out_char_ptr = out_char_ptr + CHARS_TO_WRITE; \
    if ((out_buffers_sent++ & 0x3F) == 0) \
      fprintf(stderr,"%u\r",(unsigned int)out_chars); \
  } \
}


#define write_output_buffer_delta() { \
  fflush(fd_out); \
  chars_to_write = out_char_ptr - start_char_ptr; \
  uint32_t len = out_char_ptr - start_char_ptr; \
  if (stride == 4) { \
    transpose4(start_char_ptr, len); \
    len = out_char_ptr - start_char_ptr; \
  } \
  else if (stride == 2) { \
    transpose2(start_char_ptr, len); \
    len = out_char_ptr - start_char_ptr; \
  } \
  delta_transform(start_char_ptr, len); \
  fwrite(start_char_ptr,1,chars_to_write,fd_out); \
  out_chars += chars_to_write; \
  if (out_buffer_num == 0) { \
    out_buffer_num = 1; \
    uint8_t k; \
    for (k = 1 ; k <= stride ; k++) \
      out_char1[100 - k] = *(out_char_ptr - k); \
    out_char_ptr = out_char1 + 100; \
    start_char_ptr = out_char_ptr; \
    extra_out_char_ptr = out_char_ptr + CHARS_TO_WRITE; \
  } \
  else { \
    out_buffer_num = 0; \
    uint8_t k; \
    for (k = 1 ; k <= stride ; k++) \
      out_char0[100 - k] = *(out_char_ptr - k); \
    out_char_ptr = out_char0 + 100; \
    start_char_ptr = out_char_ptr; \
    extra_out_char_ptr = out_char_ptr + CHARS_TO_WRITE; \
    if ((out_buffers_sent++ & 0x3F) == 0) \
      fprintf(stderr,"%u\r",(unsigned int)out_chars); \
  } \
}


#define write_string(len) { \
  while (out_char_ptr + len >= extra_out_char_ptr) { \
    uint32_t temp_len = extra_out_char_ptr - out_char_ptr; \
    len -= temp_len; \
    copy_string(symbol_string_ptr, temp_len, out_char_ptr); \
    write_output_buffer(); \
  } \
  copy_string(symbol_string_ptr, len, out_char_ptr); \
}


#define write_string_cap_encoded(len) { \
  while (out_char_ptr + len >= extra_out_char_ptr) { \
    uint32_t temp_len = extra_out_char_ptr - out_char_ptr; \
    len -= temp_len; \
    while (temp_len--) { \
      if (write_cap_on == 0) { \
        if (skip_space_on == 0) { \
          if ((*symbol_string_ptr & 0xFE) == 0x42) { \
            write_cap_on = 1; \
            if (*symbol_string_ptr++ == 'B') \
              write_cap_lock_on = 1; \
          } \
          else { \
            *out_char_ptr++ = *symbol_string_ptr; \
            if (*symbol_string_ptr++ == 0xA) \
              skip_space_on = 1; \
          } \
        } \
        else { \
          symbol_string_ptr++; \
          skip_space_on = 0; \
        } \
      } \
      else { \
        if (write_cap_lock_on) { \
          if ((*symbol_string_ptr >= 'a') && (*symbol_string_ptr <= 'z')) \
            *out_char_ptr++ = *symbol_string_ptr++ - 0x20; \
          else { \
            write_cap_lock_on = 0; \
            write_cap_on = 0; \
            if (*symbol_string_ptr == 'C') \
              symbol_string_ptr++; \
            else { \
              *out_char_ptr++ = *symbol_string_ptr; \
              if (*symbol_string_ptr++ == 0xA) \
                skip_space_on = 1; \
            } \
          } \
        } \
        else { \
          write_cap_on = 0; \
          *out_char_ptr++ = *symbol_string_ptr++ - 0x20; \
        } \
      } \
    } \
    write_output_buffer(); \
  } \
  while (len--) { \
    if (write_cap_on == 0) { \
      if (skip_space_on == 0) { \
        if ((*symbol_string_ptr & 0xFE) == 0x42) { \
          write_cap_on = 1; \
          if (*symbol_string_ptr++ == 'B') \
            write_cap_lock_on = 1; \
        } \
        else { \
          *out_char_ptr++ = *symbol_string_ptr; \
          if (*symbol_string_ptr++ == 0xA) \
            skip_space_on = 1; \
        } \
      } \
      else { \
        symbol_string_ptr++; \
        skip_space_on = 0; \
      } \
    } \
    else { \
      if (write_cap_lock_on) { \
        if ((*symbol_string_ptr >= 'a') && (*symbol_string_ptr <= 'z')) \
          *out_char_ptr++ = *symbol_string_ptr++ - 0x20; \
        else { \
          write_cap_lock_on = 0; \
          write_cap_on = 0; \
          if (*symbol_string_ptr == 'C') { \
            symbol_string_ptr++; \
          } \
          else { \
            *out_char_ptr++ = *symbol_string_ptr; \
            if (*symbol_string_ptr++ == 0xA) \
              skip_space_on = 1; \
          } \
        } \
      } \
      else { \
        write_cap_on = 0; \
        *out_char_ptr++ = *symbol_string_ptr++ - 0x20; \
      } \
    } \
  } \
}


#define write_string_delta(len) { \
  while (out_char_ptr + len >= extra_out_char_ptr) { \
    uint32_t temp_len = extra_out_char_ptr - out_char_ptr; \
    len -= temp_len; \
    copy_string(symbol_string_ptr, temp_len, out_char_ptr); \
    write_output_buffer_delta(); \
  } \
  copy_string(symbol_string_ptr, len, out_char_ptr); \
}


void write_single_threaded_output() {
  if (cap_encoded != 0) {
    while (symbol_buffer_read_index != symbol_buffer_write_index) {
      symbol = symbol_buffer[symbol_buffer_read_index++];
      symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
      uint32_t string_length = symbol_data[symbol].string_length;
      write_string_cap_encoded(string_length);
    }
    if (symbol_buffer_read_index == 0x200)
      symbol_buffer_read_index = 0;
  }
  else if (stride == 0) {
    while (symbol_buffer_read_index != symbol_buffer_write_index) {
      symbol = symbol_buffer[symbol_buffer_read_index++];
      symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
      uint32_t string_length = symbol_data[symbol].string_length;
      write_string(string_length);
    }
    if (symbol_buffer_read_index == 0x200)
      symbol_buffer_read_index = 0;
  }
  else {
    while (symbol_buffer_read_index != symbol_buffer_write_index) {
      symbol = symbol_buffer[symbol_buffer_read_index++];
      symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
      uint32_t string_length = symbol_data[symbol].string_length;
      write_string_delta(string_length);
    }
    if (symbol_buffer_read_index == 0x200)
      symbol_buffer_read_index = 0;
  }
  return;
}


void write_symbol() {
  symbol_buffer[symbol_buffer_write_index++] = symbol_number;
  if ((symbol_buffer_write_index & 0xFF) == 0) {
    uint8_t free_index;
    for (free_index = 0 ; free_index < free_string_list_length ; free_index++)
    if (free_string_list[free_index].wait_cycles)
      free_string_list[free_index].wait_cycles--;
    free_string_list_wait1 = free_string_list_wait2;
    free_string_list_wait2 = 0;
    while ((free_symbol_list_length < FREE_SYMBOL_LIST_SIZE) && free_symbol_list_wait1_length)
      free_symbol_list[free_symbol_list_length++] = free_symbol_list_wait1[--free_symbol_list_wait1_length];
    free_symbol_list_wait1_length = free_symbol_list_wait2_length;
    while (free_symbol_list_wait2_length) {
      free_symbol_list_wait2_length--;
      free_symbol_list_wait1[free_symbol_list_wait2_length] = free_symbol_list_wait2[free_symbol_list_wait2_length];
    }
    if (two_threads != 0) {
      if (symbol_buffer_write_index == 0x200) {
        symbol_buffer_write_index = 0;
        atomic_store_explicit(&symbol_buffer_pt2_owner, 1, memory_order_release);
        while (atomic_load_explicit(&symbol_buffer_pt1_owner, memory_order_acquire) != 0);
      }
      else {
        atomic_store_explicit(&symbol_buffer_pt1_owner, 1, memory_order_release);
        while (atomic_load_explicit(&symbol_buffer_pt2_owner, memory_order_acquire) != 0);
      }
    }
    else {
      write_single_threaded_output();
      if (symbol_buffer_write_index == 0x200)
        symbol_buffer_write_index = 0;
    }
  }
  return;
}


void *write_output_thread(void *arg) {
  uint8_t *symbol_string_ptr, *out_char_ptr;
  uint8_t write_cap_on, write_cap_lock_on, skip_space_on, next_queue_buffer;
  uint32_t symbol, *buffer_ptr, *buffer1_end_ptr, *buffer2_end_ptr;

  symbol_buffer_read_index = 0;
  if ((fd_out = fopen((char *)arg,"wb")) == NULL) {
    printf("fopen error - unable to open file '%s'\n",(char *)arg);
    exit(EXIT_FAILURE);
  }
  write_cap_on = 0;
  write_cap_lock_on = 0;
  skip_space_on = 0;
  out_buffer_num = 0;
  next_queue_buffer = 0;
  out_char_ptr = out_char0 + 100;
  start_char_ptr = out_char_ptr;
  extra_out_char_ptr = out_char_ptr + CHARS_TO_WRITE;
  buffer_ptr = &symbol_buffer[0];
  buffer1_end_ptr = &symbol_buffer[0x100];
  buffer2_end_ptr = &symbol_buffer[0x200];

  while ((atomic_load_explicit(&done_parsing, memory_order_acquire) == 0)
      && (atomic_load_explicit(&symbol_buffer_pt1_owner, memory_order_acquire) == 0));

  if (cap_encoded != 0) {
    while ((atomic_load_explicit(&done_parsing, memory_order_acquire) == 0)
        || (atomic_load_explicit(&symbol_buffer_pt1_owner, memory_order_relaxed) != 0)
        || (atomic_load_explicit(&symbol_buffer_pt2_owner, memory_order_relaxed) != 0)) {
      if (next_queue_buffer == 0) {
        if (atomic_load_explicit(&symbol_buffer_pt1_owner, memory_order_acquire) != 0) {
          do {
            symbol = *buffer_ptr++;
            symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
            uint32_t string_length = symbol_data[symbol].string_length;
            write_string_cap_encoded(string_length);
          } while (buffer_ptr != buffer1_end_ptr);
          atomic_store_explicit(&symbol_buffer_pt1_owner, 0, memory_order_release);
          next_queue_buffer = 1;
        }
      }
      else if (next_queue_buffer == 1) {
        if (atomic_load_explicit(&symbol_buffer_pt2_owner, memory_order_acquire) != 0) {
          do {
            symbol = *buffer_ptr++;
            symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
            uint32_t string_length = symbol_data[symbol].string_length;
            write_string_cap_encoded(string_length);
          } while (buffer_ptr != buffer2_end_ptr);
          atomic_store_explicit(&symbol_buffer_pt2_owner, 0, memory_order_release);
          next_queue_buffer = 0;
          buffer_ptr = &symbol_buffer[0];
        }
      }
    }
    while ((symbol = *buffer_ptr++) != MAX_U32_VALUE) {
      symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
      uint32_t string_length = symbol_data[symbol].string_length;
      write_string_cap_encoded(string_length);
    }
  }
  else if (stride == 0) {
    while ((atomic_load_explicit(&done_parsing, memory_order_acquire) == 0)
        || (atomic_load_explicit(&symbol_buffer_pt1_owner, memory_order_relaxed) != 0)
        || (atomic_load_explicit(&symbol_buffer_pt2_owner, memory_order_relaxed) != 0)) {
      if (next_queue_buffer == 0) {
        if (atomic_load_explicit(&symbol_buffer_pt1_owner, memory_order_acquire) != 0) {
          do {
            symbol = *buffer_ptr++;
            symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
            uint32_t string_length = symbol_data[symbol].string_length;
            write_string(string_length);
          } while (buffer_ptr != buffer1_end_ptr);
          atomic_store_explicit(&symbol_buffer_pt1_owner, 0, memory_order_release);
          next_queue_buffer = 1;
        }
      }
      else if (next_queue_buffer == 1) {
        if (atomic_load_explicit(&symbol_buffer_pt2_owner, memory_order_acquire) != 0) {
          do {
            symbol = *buffer_ptr++;
            symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
            uint32_t string_length = symbol_data[symbol].string_length;
            write_string(string_length);
          } while (buffer_ptr != buffer2_end_ptr);
          atomic_store_explicit(&symbol_buffer_pt2_owner, 0, memory_order_release);
          next_queue_buffer = 0;
          buffer_ptr = &symbol_buffer[0];
        }
      }
    }
    while ((symbol = *buffer_ptr++) != MAX_U32_VALUE) {
      symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
      uint32_t string_length = symbol_data[symbol].string_length;
      write_string(string_length);
    }
  }
  else {
    while ((atomic_load_explicit(&done_parsing, memory_order_acquire) == 0)
        || (atomic_load_explicit(&symbol_buffer_pt1_owner, memory_order_relaxed) != 0)
        || (atomic_load_explicit(&symbol_buffer_pt2_owner, memory_order_relaxed) != 0)) {
      if (next_queue_buffer == 0) {
        if (atomic_load_explicit(&symbol_buffer_pt1_owner, memory_order_acquire) != 0) {
          do {
            symbol = *buffer_ptr++;
            symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
            uint32_t string_length = symbol_data[symbol].string_length;
            write_string_delta(string_length);
          } while (buffer_ptr != buffer1_end_ptr);
          atomic_store_explicit(&symbol_buffer_pt1_owner, 0, memory_order_release);
          next_queue_buffer = 1;
        }
      }
      else if (next_queue_buffer == 1) {
        if (atomic_load_explicit(&symbol_buffer_pt2_owner, memory_order_acquire) != 0) {
          do {
            symbol = *buffer_ptr++;
            symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
            uint32_t string_length = symbol_data[symbol].string_length;
            write_string_delta(string_length);
          } while (buffer_ptr != buffer2_end_ptr);
          atomic_store_explicit(&symbol_buffer_pt2_owner, 0, memory_order_release);
          next_queue_buffer = 0;
          buffer_ptr = &symbol_buffer[0];
        }
      }
    }
    while ((symbol = *buffer_ptr++) != MAX_U32_VALUE) {
      symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
      uint32_t string_length = symbol_data[symbol].string_length;
      write_string_delta(string_length);
    }
  }
  chars_to_write = out_char_ptr - start_char_ptr;
  if (stride) {
    uint32_t len = chars_to_write;
    if (stride == 4) {
      transpose4(start_char_ptr, len);
      len = chars_to_write;
    }
    else if (stride == 2) {
      transpose2(start_char_ptr, len);
      len = chars_to_write;
    }
    delta_transform(start_char_ptr, len);
  }
  fwrite(start_char_ptr,1,chars_to_write,fd_out);
  fclose(fd_out);
  fprintf(stderr,"Decompressed %u bytes",(unsigned int)(out_chars+chars_to_write));
  return(0);
}


#define send_symbol() { \
  write_symbol(); \
  prior_end = symbol_data[symbol_number].ends; \
}


#define send_symbol_cap() { \
  send_symbol(); \
  prior_is_cap = (symbol_data[symbol_number].ends == 'C'); \
}


void print_usage() {
  fprintf(stderr,"ERROR - Invalid format - Use GLZAdecode [-t#] <infile> <outfile>\n");
  fprintf(stderr," where -t specifies the number of threads.  Valid values are 1 and 2 (default).\n");
  return;
}


int main(int argc, char* argv[]) {
  uint8_t arg_num, num_inst_codes, i1, i2;
  pthread_t output_thread;

  clock_t start_time = clock();

  arg_num = 1;
  if (argc < 3) {
    print_usage();
    exit(EXIT_FAILURE);
  }
  two_threads = 1;
  if (*argv[1] ==  '-') {
    two_threads = *(argv[1]+2) - '1';
    if ((*(argv[1]+1) != 't') || (two_threads > 1)) {
      fprintf(stderr,"ERROR - Invalid '-' format.  Only -t1 or -t2 (default) allowed\n");
      exit(EXIT_FAILURE);
    }
    arg_num = 2;
    if (argc < 4) {
      print_usage();
      exit(EXIT_FAILURE);
    }
  }

  out_buffers_sent = 0;
  symbol_buffer_write_index = 0;

  if (two_threads) {
    atomic_init(&done_parsing, 0);
    atomic_init(&symbol_buffer_pt1_owner, 0);
    atomic_init(&symbol_buffer_pt2_owner, 0);
    pthread_create(&output_thread,NULL,write_output_thread,argv[arg_num + 1]);
  }
  else {
    if ((fd_out = fopen(argv[arg_num + 1],"wb")) == NULL) {
      printf("fopen error - unable to open file '%s'\n",argv[arg_num + 1]);
      exit(EXIT_FAILURE);
    }
    symbol_buffer_read_index = 0;
    write_cap_on = 0;
    write_cap_lock_on = 0;
    skip_space_on = 0;
    out_buffer_num = 0;
    out_char_ptr = out_char0 + 100;
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

  if ((fd_in = fopen(argv[arg_num],"rb")) == NULL) {
    printf("fopen error - file '%s' not found\n",argv[arg_num]);
    exit(EXIT_FAILURE);
  }

  if (fread(out_char0,1,4,fd_in) != 4)
    goto finish_decode;
  cap_encoded = out_char0[0] >> 7;
  UTF8_compliant = (out_char0[0] >> 6) & 1;
  use_mtf = (out_char0[0] >> 5) & 1;
  max_code_length = (out_char0[0] & 0x1F) + 1;
  mtf_queue_miss_code_length[2] = max_code_length;
  max_regular_code_length = max_code_length - (out_char0[2] & 0x1F);
  use_mtfg = 0;
  if (use_mtf && (max_regular_code_length >= 11))
    use_mtfg = 1;
  i1 = 3;
  do {
    mtf_queue_miss_code_length[i1] = mtf_queue_miss_code_length[i1-1] - ((out_char0[1] >> (i1 + 3)) & 1);
  } while (++i1 != 5);
  do {
    mtf_queue_miss_code_length[i1] = mtf_queue_miss_code_length[i1-1] - ((out_char0[2] >> i1) & 1);
  } while (++i1 != 8);
  do {
    mtf_queue_miss_code_length[i1] = mtf_queue_miss_code_length[i1-1] - ((out_char0[3] >> (i1-8)) & 1);
  } while (++i1 != 16);
  num_inst_codes = MAX_INSTANCES_FOR_MTF_QUEUE + max_regular_code_length - (out_char0[1] & 0x1F);
  stride = 0;
  if (UTF8_compliant) {
    if (fread(out_char0,1,1,fd_in) != 1)
      goto finish_decode;
    base_bits = out_char0[0];
    num_base_symbols = 1 << base_bits;
    if (cap_encoded != 0)
      num_base_symbols -= 24;
  }
  else {
    base_bits = 8;
    num_base_symbols = 0x100;
    delta_format = (out_char0[1] & 0x20) >> 5;
    if (delta_format) {
      if (fread(out_char0,1,1,fd_in) != 1)
        goto finish_decode;
      delta_format = out_char0[0];
      if ((delta_format & 0x80) == 0)
        stride = (delta_format & 0x3) + 1;
      else
        stride = delta_format & 0x7F;
    }
  }

  symbol_data[MAX_SYMBOLS_DEFINED - 1].type = 0;
  uint8_t * lookup_bits_ptr = &lookup_bits[0x100][0x1000];
  while (lookup_bits_ptr-- != &lookup_bits[0][0])
    *lookup_bits_ptr = max_code_length;
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

  InitDecoder(fd_in, max_regular_code_length, num_inst_codes);
  i1 = 0xFF;
  if (UTF8_compliant)
    i1 = 0x80;
  do {
    for (i2 = max_code_length ; i2 >= 2 ; i2--) {
      sym_list_bits[i1][i2] = 2;
      if (0 == (sym_list_ptrs[i1][i2] = (uint32_t *)malloc(sizeof(uint32_t) * 4))) {
        fprintf(stderr,"FATAL ERROR - symbol list malloc failure\n"); \
        exit(EXIT_FAILURE);
      }
      nsob[i1][i2] = 0;
      nbob[i1][i2] = 0;
      fbob[i1][i2] = 0;
    }
    sum_nbob[i1] = 0;
    symbol_lengths[i1] = 0;
    bin_code_length[i1] = max_code_length;
  } while (i1--);
  find_first_symbol = 1;
  free_string_list_length = 0;
  free_string_list_wait1 = 0;
  free_string_list_wait2 = 0;
  free_symbol_list_length = 0;
  free_symbol_list_wait1_length = 0;
  free_symbol_list_wait2_length = 0;

  dictionary_size = 0x1000000;
  if (0 == (symbol_strings = (uint8_t *)malloc(dictionary_size))) {
    fprintf(stderr,"FATAL ERROR - dictionary malloc failure\n"); \
    exit(EXIT_FAILURE);
  }

  // main decoding loop
  if (cap_encoded != 0) {
    cap_symbol_defined = 0;
    cap_lock_symbol_defined = 0;
    while (1) {
      if (prior_is_cap == 0) {
        DecodeSymTypeStart(LEVEL0);
        if (DecodeSymTypeCheckDict(LEVEL0)) { // dictionary symbol
          DecodeSymTypeFinishDict(LEVEL0);
          if (prior_end != 0xA) {
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
          }
          else
            FirstChar = ' ';
          DictionaryBins = sum_nbob[FirstChar];
          DecodeDictionaryBin(lookup_bits[FirstChar]);
          if (CodeLength > bin_code_length[FirstChar]) {
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
        else if (DecodeSymTypeCheckNew(LEVEL0)) {
          DecodeSymTypeFinishNew(LEVEL0);
          no_embed = 1;
          decode_define_cap_encoded(symbol_data[num_symbols_defined].string_index);
          write_symbol();
        }
        else {
          if (DecodeSymTypeCheckMtfg(LEVEL0)) {
            DecodeSymTypeFinishMtfg(LEVEL0);
            get_mtfg_symbol();
          }
          else {
            DecodeSymTypeFinishMtf(LEVEL0);
            get_mtf_symbol();
          }
          send_symbol_cap();
        }
      }
      else { // prior_is_cap
        DecodeSymTypeStart(LEVEL0_CAP);
        if (DecodeSymTypeCheckDict(LEVEL0_CAP)) { // dictionary symbol
          DecodeSymTypeFinishDict(LEVEL0_CAP);
          DecodeFirstChar(0, 'C');
          DictionaryBins = sum_nbob[FirstChar];
          DecodeDictionaryBin(lookup_bits[FirstChar]);
          if (CodeLength > bin_code_length[FirstChar]) {
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
          else if (symbol_data[symbol_number].type & 4) {
            add_new_symbol_to_mtfg_queue(symbol_number);
          }
        }
        else if (DecodeSymTypeCheckNew(LEVEL0_CAP)) {
          DecodeSymTypeFinishNew(LEVEL0_CAP);
          no_embed = 1;
          decode_define_cap_encoded(symbol_data[num_symbols_defined].string_index);
          write_symbol();
        }
        else {
          if (DecodeSymTypeCheckMtfg(LEVEL0_CAP)) {
            DecodeSymTypeFinishMtfg(LEVEL0_CAP);
            get_mtfg_symbol_cap();
          }
          else {
            DecodeSymTypeFinishMtf(LEVEL0_CAP);
            get_mtf_symbol_cap();
          }
          send_symbol_cap();
        }
      }
    }
  }
  else { // not cap encoded
    while (1) {
      DecodeSymTypeStart(LEVEL0);
      if (DecodeSymTypeCheckDict(LEVEL0)) { // dictionary symbol
        DecodeSymTypeFinishDict(LEVEL0);
        if (UTF8_compliant) {
          DecodeFirstChar(0, prior_end);
        }
        else {
          DecodeFirstCharBinary(prior_end);
        }
        DictionaryBins = sum_nbob[FirstChar];
        DecodeDictionaryBin(lookup_bits[FirstChar]);
        if (CodeLength > bin_code_length[FirstChar]) {
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
            check_free_symbol();
          }
        }
        else if (symbol_data[symbol_number].type & 0x4) {
          add_new_symbol_to_mtfg_queue(symbol_number);
        }
      }
      else if (DecodeSymTypeCheckNew(LEVEL0)) {
        DecodeSymTypeFinishNew(LEVEL0);
        no_embed = 1;
        decode_define(symbol_data[num_symbols_defined].string_index);
        write_symbol();
      }
      else {
        if (DecodeSymTypeCheckMtfg(LEVEL0)) {
          DecodeSymTypeFinishMtfg(LEVEL0);
          get_mtfg_symbol();
        }
        else {
          DecodeSymTypeFinishMtf(LEVEL0);
          get_mtf_symbol();
        }
        send_symbol();
      }
    }
  }

finish_decode:
  symbol_buffer[symbol_buffer_write_index] = MAX_U32_VALUE;
  if (two_threads)
    atomic_store_explicit(&done_parsing, 1, memory_order_release);
  i1 = 0xFF;
  if (UTF8_compliant)
    i1 = 0x80;
  do {
    for (i2 = max_code_length ; i2 >= 2 ; i2--)
      free(sym_list_ptrs[i1][i2]);
  } while (i1--);
  fclose(fd_in);
  if (two_threads) {
    pthread_join(output_thread,NULL);
  }
  else {
    write_single_threaded_output();
    chars_to_write = out_char_ptr - start_char_ptr;
    if (stride) { \
      uint32_t len = out_char_ptr - start_char_ptr; \
      if (stride == 4) { \
        transpose4(start_char_ptr, len); \
        len = out_char_ptr - start_char_ptr; \
      } \
      else if (stride == 2) { \
        transpose2(start_char_ptr, len); \
        len = out_char_ptr - start_char_ptr; \
      } \
      delta_transform(start_char_ptr, len); \
    } \
    fwrite(start_char_ptr,1,chars_to_write,fd_out);
    fclose(fd_out);
    fprintf(stderr,"Decompressed %u bytes",(unsigned int)(out_chars+chars_to_write));
  }
  fprintf(stderr," in %.3f seconds\n",(float)(clock()-start_time)/CLOCKS_PER_SEC);
  return(0);
}