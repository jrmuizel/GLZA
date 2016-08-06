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

// GLZAencode.c
//   Encodes files created by GLZAcompress
//
// Usage:
//   GLZAencode [-m#] [-v#] <infilename> <outfilename>, where
//       -m# overrides the programs decision on whether to use mtf.  -m0 disables mtf, -m1 enables mtf
//       -v0 prints the dictionary to stdout, most frequent first
//       -v1 prints the dicitonary to stdout, simple symbols followed by complex symbols in the order they were created


#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include "GLZA.h"
#define encode

const U8 MAX_BITS_IN_CODE = 25;
const U8 INSERT_SYMBOL_CHAR = 0xFE;
const U8 DEFINE_SYMBOL_CHAR = 0xFF;
const U32 UNIQUE_CHAR = 0xFFFFFFFF;
const U32 START_UTF8_2BYTE_SYMBOLS = 0x80;
const U32 START_UTF8_3BYTE_SYMBOLS = 0x800;
const U32 START_UTF8_4BYTE_SYMBOLS = 0x10000;
const U32 READ_SIZE = 0x80000;
const U32 MAX_FILE_SIZE = 1100000000;
const U32 MAX_INSTANCES_FOR_MTF_QUEUE = 15;
const U32 MTF_QUEUE_SIZE = 64;
const U32 MAX_SYMBOLS_DEFINED = 0x00900000;

U8 UTF8_compliant, base_bits, cap_encoded, prior_is_cap, use_mtf, delta_format, stride, found_first_symbol, end_symbol;
U8 symbol_code_length, symbol_bits, temp_bits, max_code_length, max_regular_code_length;
U8 cap_symbol_defined, cap_lock_symbol_defined;
U8 mtfg_queue_8_offset, mtfg_queue_16_offset, mtfg_queue_32_offset;
U8 mtfg_queue_64_offset, mtfg_queue_128_offset, mtfg_queue_192_offset;
U8 nbob_shift[0x101], sym_list_bits[0x100][26], mtf_queue_overflow_code_length[16];
U8 *in_char_ptr, *end_char_ptr;
U8 in_data[0x80003];
U16 fbob[0x100][26];
U32 num_define_symbols_written, num_grammar_rules, num_symbols_to_code, mtf_queue_miss_code_space, min_extra_reduce_index;
U32 symbol_index, end_symbols, symbol_to_move, prior_end, rules_reduced, start_my_symbols;
U32 symbol_lengths[0x100], nsob[0x100][26], nbob[0x100][26], sum_nbob[0x100];
U32 mtf_queue[16][65], mtf_queue_hit_count[16][65];
U32 mtf_queue_started[16], mtf_queue_done[16], mtf_queue_peak[16], mtf_queue_size[16];
U32 mtfg_queue_0[8], mtfg_queue_8[8], mtfg_queue_16[0x10], mtfg_queue_32[0x20];
U32 mtfg_queue_64[0x40], mtfg_queue_128[0x40], mtfg_queue_192[0x40];
U32 *mtf_queue_ptr, *mtf_queue_end_ptr;
U32 *symbol, *symbol_ptr, *ranked_symbols, *first_define_ptr = 0;
U32 *sym_list_ptrs[0x100][26];
S32 prior_symbol;

// type:  bit 0: string ends 'C' or 'B' (cap symbol/cap lock symbol), bit1: string starts a-z, bit 2: non-ergodic, bit 3: in queue
// bit 4: "word"ness determined, bit 5: "word", bit 6: mtfg word, bit 7: mtfg word likely to be followed by ' '
struct symbol_data {
  U8 starts, ends, code_length, type;
  U32 count, inst_found, array_index, mtfg_hits, hit_score, define_symbol_start_index;
  S32 space_score;
} *sd;

#include "GLZAmodel.h"



void print_string(U32 symbol_number) {
  U32 *symbol_ptr, *next_symbol_ptr;
  if (symbol_number < start_my_symbols) {
    if (UTF8_compliant) {
      if (symbol_number < START_UTF8_2BYTE_SYMBOLS)
        printf("%c",(unsigned char)symbol_number);
      else if (symbol_number < START_UTF8_3BYTE_SYMBOLS) {
        printf("%c",(unsigned char)(symbol_number >> 6) + 0xC0);
        printf("%c",(unsigned char)(symbol_number & 0x3F) + 0x80);
      }
      else if (symbol_number < START_UTF8_4BYTE_SYMBOLS) {
        printf("%c",(unsigned char)(symbol_number >> 12) + 0xE0);
        printf("%c",(unsigned char)((symbol_number >> 6) & 0x3F) + 0x80);
        printf("%c",(unsigned char)(symbol_number & 0x3F) + 0x80);
      }
      else {
        printf("%c",(unsigned char)(symbol_number >> 18) + 0xF0);
        printf("%c",(unsigned char)((symbol_number >> 12) & 0x3F) + 0x80);
        printf("%c",(unsigned char)((symbol_number >> 6) & 0x3F) + 0x80);
        printf("%c",(unsigned char)(symbol_number & 0x3F) + 0x80);
      }
    }
    else
      printf("%c",(unsigned char)symbol_number);
  }
  else {
    symbol_ptr = symbol + sd[symbol_number].define_symbol_start_index;
    next_symbol_ptr = symbol + sd[symbol_number+1].define_symbol_start_index - 1;
    while (symbol_ptr != next_symbol_ptr)
      print_string(*symbol_ptr++);
  }
  return;
}


void print_string2(U32 symbol_number) {
  U32 *symbol_ptr, *next_symbol_ptr;
  if (symbol_number < start_my_symbols) {
    if (UTF8_compliant) {
      if (symbol_number < START_UTF8_2BYTE_SYMBOLS)
        fprintf(stderr,"%c",(unsigned char)symbol_number);
      else if (symbol_number < START_UTF8_3BYTE_SYMBOLS) {
        fprintf(stderr,"%c",(unsigned char)(symbol_number >> 6) + 0xC0);
        fprintf(stderr,"%c",(unsigned char)(symbol_number & 0x3F) + 0x80);
      }
      else if (symbol_number < START_UTF8_4BYTE_SYMBOLS) {
        fprintf(stderr,"%c",(unsigned char)(symbol_number >> 12) + 0xE0);
        fprintf(stderr,"%c",(unsigned char)((symbol_number >> 6) & 0x3F) + 0x80);
        fprintf(stderr,"%c",(unsigned char)(symbol_number & 0x3F) + 0x80);
      }
      else {
        fprintf(stderr,"%c",(unsigned char)(symbol_number >> 18) + 0xF0);
        fprintf(stderr,"%c",(unsigned char)((symbol_number >> 12) & 0x3F) + 0x80);
        fprintf(stderr,"%c",(unsigned char)((symbol_number >> 6) & 0x3F) + 0x80);
        fprintf(stderr,"%c",(unsigned char)(symbol_number & 0x3F) + 0x80);
      }
    }
    else
      fprintf(stderr,"%c",(unsigned char)symbol_number);
  }
  else {
    symbol_ptr = symbol + sd[symbol_number].define_symbol_start_index;
    next_symbol_ptr = symbol + sd[symbol_number+1].define_symbol_start_index - 1;
    while (symbol_ptr != next_symbol_ptr)
      print_string2(*symbol_ptr++);
  }
  return;
}


U32 get_string_length(U32 symbol_number) {
  U32 *symbol_ptr, *next_symbol_ptr;
  if (symbol_number < start_my_symbols) {
    if (UTF8_compliant) {
      if (symbol_number < START_UTF8_2BYTE_SYMBOLS)
        return(1);
      else if (symbol_number < START_UTF8_3BYTE_SYMBOLS)
        return(2);
      else if (symbol_number < START_UTF8_4BYTE_SYMBOLS)
        return(3);
      else
        return(4);
    }
    else
      return(1);
  }
  else {
    symbol_ptr = symbol + sd[symbol_number].define_symbol_start_index;
    next_symbol_ptr = symbol + sd[symbol_number+1].define_symbol_start_index - 1;
    U32 string_length = 0;
    while (symbol_ptr != next_symbol_ptr)
      string_length += get_string_length(*symbol_ptr++);
    return(string_length);
  }
}


void get_symbol_category(U32 symbol_number, U8 *sym_type_ptr) {
  if (symbol_number >= start_my_symbols) {
    U32 * string_ptr;
    string_ptr = symbol + sd[symbol_number+1].define_symbol_start_index - 2;
    get_symbol_category(*string_ptr, sym_type_ptr);
    while (((*sym_type_ptr & 0x10) == 0) && (string_ptr != symbol + sd[symbol_number].define_symbol_start_index))
      get_symbol_category(*--string_ptr, sym_type_ptr);
  }
  else if (symbol_number == (U32)' ')
    *sym_type_ptr |= 0x30;
  return;
}


U8 find_first(U32 symbol_number) {
  U8 first_char;
  U32 first_symbol = symbol[sd[symbol_number].define_symbol_start_index];
  if (first_symbol >= start_my_symbols) {
    if ((first_char = sd[first_symbol].starts) == 0) {
      first_char = find_first(first_symbol);
      sd[first_symbol].starts = first_char;
    }
    return(first_char);
  }
  return((U8)first_symbol);
}


U8 find_first_UTF8(U32 symbol_number) {
  U8 first_char;
  U32 first_symbol = symbol[sd[symbol_number].define_symbol_start_index];
  if (first_symbol >= start_my_symbols) {
    if ((first_char = sd[first_symbol].starts) == 0) {
      first_char = find_first_UTF8(first_symbol);
      sd[first_symbol].starts = first_char;
    }
    return(first_char);
  }
  if (first_symbol < 0x80)
    return((U8)first_symbol);
  return(0x80);
}


U8 find_last(U32 symbol_number) {
  U8 last_char;
  U32 last_symbol = symbol[sd[symbol_number+1].define_symbol_start_index - 2];
  if (last_symbol >= start_my_symbols) {
    if ((last_char = sd[last_symbol].ends) == 0) {
      last_char = find_last(last_symbol);
      sd[last_symbol].ends = last_char;
    }
    return(last_char);
  }
  if (cap_encoded && (last_symbol == 'B'))
    return('C');
  return((U8)last_symbol);
}


U8 find_last_UTF8(U32 symbol_number) {
  U8 last_char;
  U32 last_symbol = symbol[sd[symbol_number+1].define_symbol_start_index - 2];
  if (last_symbol >= start_my_symbols) {
    if ((last_char = sd[last_symbol].ends) == 0) {
      last_char = find_last_UTF8(last_symbol);
      sd[last_symbol].ends = last_char;
    }
    return(last_char);
  }
  if (cap_encoded && (last_symbol == 'B'))
    return('C');
  if (last_symbol < 0x80)
    return((U8)last_symbol);
  return(0x80);
}


#define remove_mtfg_queue_symbol_16() { \
  U8 qp = mtfg_queue_position - 16; \
  while (qp != 15) { \
    *(mtfg_queue_16 + ((mtfg_queue_16_offset + qp) & 0xF)) = *(mtfg_queue_16 + ((mtfg_queue_16_offset + qp + 1) & 0xF)); \
    qp++; \
  } \
  *(mtfg_queue_16 + ((mtfg_queue_16_offset - 1) & 0xF)) = *(mtfg_queue_32 + mtfg_queue_32_offset); \
  *(mtfg_queue_32 + mtfg_queue_32_offset) = *(mtfg_queue_64 + mtfg_queue_64_offset); \
  mtfg_queue_32_offset = (mtfg_queue_32_offset + 1) & 0x1F; \
  *(mtfg_queue_64 + mtfg_queue_64_offset) = *(mtfg_queue_128 + mtfg_queue_128_offset); \
  mtfg_queue_64_offset = (mtfg_queue_64_offset + 1) & 0x3F; \
  *(mtfg_queue_128 + mtfg_queue_128_offset) = *(mtfg_queue_192 + mtfg_queue_192_offset); \
  mtfg_queue_128_offset = (mtfg_queue_128_offset + 1) & 0x3F; \
  *(mtfg_queue_192 + mtfg_queue_192_offset) = end_symbols; \
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F; \
}


#define remove_mtfg_queue_symbol_32() { \
  U8 qp = mtfg_queue_position - 32; \
  while (qp != 31) { \
    *(mtfg_queue_32 + ((mtfg_queue_32_offset + qp) & 0x1F)) = *(mtfg_queue_32 + ((mtfg_queue_32_offset + qp + 1) & 0x1F)); \
    qp++; \
  } \
  *(mtfg_queue_32 + ((mtfg_queue_32_offset - 1) & 0x1F)) = *(mtfg_queue_64 + mtfg_queue_64_offset); \
  *(mtfg_queue_64 + mtfg_queue_64_offset) = *(mtfg_queue_128 + mtfg_queue_128_offset); \
  mtfg_queue_64_offset = (mtfg_queue_64_offset + 1) & 0x3F; \
  *(mtfg_queue_128 + mtfg_queue_128_offset) = *(mtfg_queue_192 + mtfg_queue_192_offset); \
  mtfg_queue_128_offset = (mtfg_queue_128_offset + 1) & 0x3F; \
  *(mtfg_queue_192 + mtfg_queue_192_offset) = end_symbols; \
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F; \
}


#define remove_mtfg_queue_symbol_64() { \
  U8 qp = mtfg_queue_position - 64; \
  while (qp != 63) { \
    *(mtfg_queue_64 + ((mtfg_queue_64_offset + qp) & 0x3F)) = *(mtfg_queue_64 + ((mtfg_queue_64_offset + qp + 1) & 0x3F)); \
    qp++; \
  } \
  *(mtfg_queue_64 + ((mtfg_queue_64_offset - 1) & 0x3F)) = *(mtfg_queue_128 + mtfg_queue_128_offset); \
  *(mtfg_queue_128 + mtfg_queue_128_offset) = *(mtfg_queue_192 + mtfg_queue_192_offset); \
  mtfg_queue_128_offset = (mtfg_queue_128_offset + 1) & 0x3F; \
  *(mtfg_queue_192 + mtfg_queue_192_offset) = end_symbols; \
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F; \
}


#define remove_mtfg_queue_symbol_128() { \
  U8 qp = mtfg_queue_position - 128; \
  while (qp != 63) { \
    *(mtfg_queue_128 + ((mtfg_queue_128_offset + qp) & 0x3F)) \
        = *(mtfg_queue_128 + ((mtfg_queue_128_offset + qp + 1) & 0x3F)); \
    qp++; \
  } \
  *(mtfg_queue_128 + ((mtfg_queue_128_offset - 1) & 0x3F)) = *(mtfg_queue_192 + mtfg_queue_192_offset); \
  *(mtfg_queue_192 + mtfg_queue_192_offset) = end_symbols; \
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F; \
}


#define remove_mtfg_queue_symbol_192() { \
  U8 qp = mtfg_queue_position - 192; \
  while (qp != 63) { \
    *(mtfg_queue_192 + ((mtfg_queue_192_offset + qp) & 0x3F)) \
        = *(mtfg_queue_192 + ((mtfg_queue_192_offset + qp + 1) & 0x3F)); \
    qp++; \
  } \
  *(mtfg_queue_192 + ((mtfg_queue_192_offset + qp) & 0x3F)) = end_symbols; \
}


#define increment_mtfg_queue_0(symbol_number) { \
  mtfg_queue_symbol_7 = mtfg_queue_0[7]; \
  mtfg_queue_0[7] = mtfg_queue_0[6]; \
  mtfg_queue_0[6] = mtfg_queue_0[5]; \
  mtfg_queue_0[5] = mtfg_queue_0[4]; \
  mtfg_queue_0[4] = mtfg_queue_0[3]; \
  mtfg_queue_0[3] = mtfg_queue_0[2]; \
  mtfg_queue_0[2] = mtfg_queue_0[1]; \
  mtfg_queue_0[1] = mtfg_queue_0[0]; \
  mtfg_queue_0[0] = symbol_number; \
}


#define increment_mtfg_queue_8() { \
  mtfg_queue_8_offset = (mtfg_queue_8_offset - 1) & 7; \
  mtfg_queue_symbol_15 = *(mtfg_queue_8 + mtfg_queue_8_offset); \
  *(mtfg_queue_8 + mtfg_queue_8_offset) = mtfg_queue_symbol_7; \
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
  sd[*(mtfg_queue_192 + mtfg_queue_192_offset)].type &= 0xF7; \
  *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191; \
}


#define add_symbol_to_mtfg_queue(symbol_number) { \
  sd[symbol_number].type |= 8; \
  U32 mtfg_queue_symbol_7, mtfg_queue_symbol_15; \
  increment_mtfg_queue_0(symbol_number); \
  increment_mtfg_queue_8(); \
  if (sd[mtfg_queue_symbol_15].code_length > 12) { \
    U32 mtfg_queue_symbol_31; \
    increment_mtfg_queue_16(); \
    if (sd[mtfg_queue_symbol_31].code_length != 13) { \
      U32 mtfg_queue_symbol_63; \
      increment_mtfg_queue_32(); \
      if (sd[mtfg_queue_symbol_63].code_length != 14) { \
        U32 mtfg_queue_symbol_127; \
        increment_mtfg_queue_64(); \
        if (sd[mtfg_queue_symbol_127].code_length != 15) { \
          U32 mtfg_queue_symbol_191; \
          increment_mtfg_queue_128(); \
          if (sd[mtfg_queue_symbol_191].code_length != 16) { \
            increment_mtfg_queue_192(); \
          } \
          else \
            sd[mtfg_queue_symbol_191].type &= 0xF7; \
        } \
        else \
          sd[mtfg_queue_symbol_127].type &= 0xF7; \
      } \
      else \
        sd[mtfg_queue_symbol_63].type &= 0xF7; \
    } \
    else \
      sd[mtfg_queue_symbol_31].type &= 0xF7; \
  } \
  else \
    sd[mtfg_queue_symbol_15].type &= 0xF7; \
}


#define manage_mtfg_queue1(symbol_number) { \
  U8 mtfg_queue_position; \
  U32 subqueue_position; \
  mtfg_queue_position = 0; \
  do { \
    if (symbol_number == mtfg_queue_0[mtfg_queue_position]) { \
      sd[symbol_number].hit_score += 15; \
      while (mtfg_queue_position) { \
        mtfg_queue_0[mtfg_queue_position] = mtfg_queue_0[mtfg_queue_position-1]; \
        mtfg_queue_position--; \
      } \
      mtfg_queue_0[0] = symbol_number; \
      break; \
    } \
    mtfg_queue_position++; \
  } while (mtfg_queue_position != 5); \
  if (mtfg_queue_position == 5) { \
    do { \
      if (symbol_number == mtfg_queue_0[mtfg_queue_position]) { \
        sd[symbol_number].hit_score += 10; \
        while (mtfg_queue_position != 5) { \
          mtfg_queue_0[mtfg_queue_position] = mtfg_queue_0[mtfg_queue_position-1]; \
          mtfg_queue_position--; \
        } \
        mtfg_queue_0[5] = mtfg_queue_0[4]; \
        mtfg_queue_0[4] = mtfg_queue_0[3]; \
        mtfg_queue_0[3] = mtfg_queue_0[2]; \
        mtfg_queue_0[2] = mtfg_queue_0[1]; \
        mtfg_queue_0[1] = mtfg_queue_0[0]; \
        mtfg_queue_0[0] = symbol_number; \
        break; \
      } \
      mtfg_queue_position++; \
    } while (mtfg_queue_position != 8); \
    if (mtfg_queue_position == 8) { \
      sd[symbol_number].hit_score += 6; \
      U32 mtfg_queue_symbol_7; \
      increment_mtfg_queue_0(symbol_number); \
      do { \
        if (symbol_number == *(mtfg_queue_8 + ((mtfg_queue_position + mtfg_queue_8_offset) & 7))) { \
          subqueue_position = mtfg_queue_position - 8; \
          while (subqueue_position) { \
            *(mtfg_queue_8 + ((mtfg_queue_8_offset + subqueue_position) & 7)) \
                = *(mtfg_queue_8 + ((mtfg_queue_8_offset + subqueue_position - 1) & 7)); \
            subqueue_position--; \
          } \
          *(mtfg_queue_8 + mtfg_queue_8_offset) = mtfg_queue_symbol_7; \
          break; \
        } \
        mtfg_queue_position++; \
      } while (mtfg_queue_position != 16); \
      if (mtfg_queue_position == 16) { \
        sd[symbol_number].hit_score += 4; \
        U32 mtfg_queue_symbol_15; \
        increment_mtfg_queue_8(); \
        do { \
          if (symbol_number == *(mtfg_queue_16 + ((mtfg_queue_position + mtfg_queue_16_offset) & 0xF))) { \
            if (sd[mtfg_queue_symbol_15].code_length <= 12) { \
              sd[mtfg_queue_symbol_15].type &= 0xF7; \
              remove_mtfg_queue_symbol_16(); \
            } \
            else { \
              subqueue_position = mtfg_queue_position - 16; \
              while (subqueue_position) { \
                *(mtfg_queue_16 + ((mtfg_queue_16_offset + subqueue_position) & 0xF)) \
                    = *(mtfg_queue_16 + ((mtfg_queue_16_offset + subqueue_position - 1) & 0xF)); \
                subqueue_position--; \
              } \
              *(mtfg_queue_16 + mtfg_queue_16_offset) = mtfg_queue_symbol_15; \
            } \
            break; \
          } \
          mtfg_queue_position++; \
        } while (mtfg_queue_position != 32); \
        if (mtfg_queue_position == 32) { \
          do { \
            if (symbol_number == *(mtfg_queue_32 + ((mtfg_queue_position + mtfg_queue_32_offset) & 0x1F))) { \
              sd[symbol_number].hit_score += 2; \
              if (sd[mtfg_queue_symbol_15].code_length <= 12) { \
                sd[mtfg_queue_symbol_15].type &= 0xF7; \
                remove_mtfg_queue_symbol_32(); \
              } \
              else { \
                U32 mtfg_queue_symbol_31; \
                increment_mtfg_queue_16(); \
                if (sd[mtfg_queue_symbol_31].code_length == 13) \
                { \
                  sd[mtfg_queue_symbol_31].type &= 0xF7; \
                  remove_mtfg_queue_symbol_32(); \
                } \
                else { \
                  subqueue_position = mtfg_queue_position - 32; \
                  while (subqueue_position) { \
                    *(mtfg_queue_32 + ((mtfg_queue_32_offset + subqueue_position) & 0x1F)) \
                        = *(mtfg_queue_32 + ((mtfg_queue_32_offset + subqueue_position - 1) & 0x1F)); \
                    subqueue_position--; \
                  } \
                  *(mtfg_queue_32 + mtfg_queue_32_offset) = mtfg_queue_symbol_31; \
                } \
              } \
              break; \
            } \
            mtfg_queue_position++; \
          } while (mtfg_queue_position != 64); \
          if (mtfg_queue_position == 64) { \
            sd[symbol_number].hit_score++; \
            do { \
              if (symbol_number == *(mtfg_queue_64 + ((mtfg_queue_position + mtfg_queue_64_offset) & 0x3F))) { \
                if (sd[mtfg_queue_symbol_15].code_length <= 12) { \
                  sd[mtfg_queue_symbol_15].type &= 0xF7; \
                  remove_mtfg_queue_symbol_64(); \
                } \
                else { \
                  U32 mtfg_queue_symbol_31; \
                  increment_mtfg_queue_16(); \
                  if (sd[mtfg_queue_symbol_31].code_length == 13) { \
                    sd[mtfg_queue_symbol_31].type &= 0xF7; \
                    remove_mtfg_queue_symbol_64(); \
                  } \
                  else { \
                    U32 mtfg_queue_symbol_63; \
                    increment_mtfg_queue_32(); \
                    if (sd[mtfg_queue_symbol_63].code_length == 14) { \
                      sd[mtfg_queue_symbol_63].type &= 0xF7; \
                      remove_mtfg_queue_symbol_64(); \
                    } \
                    else { \
                      subqueue_position = mtfg_queue_position - 64; \
                      while (subqueue_position) { \
                        *(mtfg_queue_64 + ((mtfg_queue_64_offset + subqueue_position) & 0x3F)) \
                            = *(mtfg_queue_64 + ((mtfg_queue_64_offset + subqueue_position - 1) & 0x3F)); \
                        subqueue_position--; \
                      } \
                      *(mtfg_queue_64 + mtfg_queue_64_offset) = mtfg_queue_symbol_63; \
                    } \
                  } \
                } \
                break; \
              } \
              mtfg_queue_position++; \
            } while (mtfg_queue_position != 128); \
            if (mtfg_queue_position == 128) { \
              do { \
                if (symbol_number == *(mtfg_queue_128 + ((mtfg_queue_position + mtfg_queue_128_offset) & 0x3F))) { \
                  if (sd[mtfg_queue_symbol_15].code_length <= 12) { \
                    sd[mtfg_queue_symbol_15].type &= 0xF7; \
                    remove_mtfg_queue_symbol_128(); \
                  } \
                  else { \
                    U32 mtfg_queue_symbol_31; \
                    increment_mtfg_queue_16(); \
                    if (sd[mtfg_queue_symbol_31].code_length == 13) { \
                      sd[mtfg_queue_symbol_31].type &= 0xF7; \
                      remove_mtfg_queue_symbol_128(); \
                    } \
                    else { \
                      U32 mtfg_queue_symbol_63; \
                      increment_mtfg_queue_32(); \
                      if (sd[mtfg_queue_symbol_63].code_length == 14) { \
                        sd[mtfg_queue_symbol_63].type &= 0xF7; \
                        remove_mtfg_queue_symbol_128(); \
                      } \
                      else { \
                        U32 mtfg_queue_symbol_127; \
                        increment_mtfg_queue_64(); \
                        if (sd[mtfg_queue_symbol_127].code_length == 15) { \
                          sd[mtfg_queue_symbol_127].type &= 0xF7; \
                          remove_mtfg_queue_symbol_128(); \
                        } \
                        else { \
                          subqueue_position = mtfg_queue_position - 128; \
                          while (subqueue_position) { \
                            *(mtfg_queue_128 + ((mtfg_queue_128_offset + subqueue_position) & 0x3F)) \
                                = *(mtfg_queue_128 + ((mtfg_queue_128_offset + subqueue_position - 1) & 0x3F)); \
                            subqueue_position--; \
                          } \
                          *(mtfg_queue_128 + mtfg_queue_128_offset) = mtfg_queue_symbol_127; \
                        } \
                      } \
                    } \
                  } \
                  break; \
                } \
                mtfg_queue_position++; \
              } while (mtfg_queue_position != 192); \
              if (mtfg_queue_position == 192) { \
                while (symbol_number != *(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F))) \
                  mtfg_queue_position++; \
                if (sd[mtfg_queue_symbol_15].code_length <= 12) { \
                  sd[mtfg_queue_symbol_15].type &= 0xF7; \
                  remove_mtfg_queue_symbol_192(); \
                } \
                else { \
                  U32 mtfg_queue_symbol_31; \
                  increment_mtfg_queue_16(); \
                  if (sd[mtfg_queue_symbol_31].code_length == 13) { \
                    sd[mtfg_queue_symbol_31].type &= 0xF7; \
                    remove_mtfg_queue_symbol_192(); \
                  } \
                  else { \
                    U32 mtfg_queue_symbol_63; \
                    increment_mtfg_queue_32(); \
                    if (sd[mtfg_queue_symbol_63].code_length == 14) { \
                      sd[mtfg_queue_symbol_63].type &= 0xF7; \
                      remove_mtfg_queue_symbol_192(); \
                    } \
                    else { \
                      U32 mtfg_queue_symbol_127; \
                      increment_mtfg_queue_64(); \
                      if (sd[mtfg_queue_symbol_127].code_length == 15) { \
                        sd[mtfg_queue_symbol_127].type &= 0xF7; \
                        remove_mtfg_queue_symbol_192(); \
                      } \
                      else { \
                        U32 mtfg_queue_symbol_191; \
                        increment_mtfg_queue_128(); \
                        if (sd[mtfg_queue_symbol_191].code_length == 16) { \
                          sd[mtfg_queue_symbol_191].type &= 0xF7; \
                          remove_mtfg_queue_symbol_192(); \
                        } \
                        else { \
                          subqueue_position = mtfg_queue_position - 192; \
                          while (subqueue_position) { \
                            *(mtfg_queue_192 + ((mtfg_queue_192_offset + subqueue_position) & 0x3F)) \
                                = *(mtfg_queue_192 + ((mtfg_queue_192_offset + subqueue_position - 1) & 0x3F)); \
                            subqueue_position--; \
                          } \
                          *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191; \
} } } } } } } } } } } } } \


#define manage_mtfg_queue(symbol_number, in_definition) { \
  U8 mtfg_queue_position = 0; \
  U8 cap_queue_position = 0; \
  U8 subqueue_position; \
  do { \
    if (symbol_number == mtfg_queue_0[mtfg_queue_position]) { \
      if (in_definition == 0) { \
        EncodeMtfgType(LEVEL0); \
      } \
      else { \
        EncodeMtfgType(LEVEL1); \
      } \
      EncodeMtfgQueuePos(NOT_CAP); \
      while (mtfg_queue_position) { \
        mtfg_queue_0[mtfg_queue_position] = mtfg_queue_0[mtfg_queue_position-1]; \
        mtfg_queue_position--; \
      } \
      mtfg_queue_0[0] = symbol_number; \
      break; \
    } \
  } while (++mtfg_queue_position != 8); \
  if (mtfg_queue_position == 8) { \
    U32 mtfg_queue_symbol_7; \
    increment_mtfg_queue_0(symbol_number); \
    do { \
      if (symbol_number == *(mtfg_queue_8 + ((mtfg_queue_position + mtfg_queue_8_offset) & 7))) { \
        if (in_definition == 0) { \
          EncodeMtfgType(LEVEL0); \
        } \
        else { \
          EncodeMtfgType(LEVEL1); \
        } \
        EncodeMtfgQueuePos(NOT_CAP); \
        subqueue_position = mtfg_queue_position - 8; \
        while (subqueue_position) { \
          *(mtfg_queue_8 + ((mtfg_queue_8_offset + subqueue_position) & 7)) \
              = *(mtfg_queue_8 + ((mtfg_queue_8_offset + subqueue_position - 1) & 7)); \
          subqueue_position--; \
        } \
        *(mtfg_queue_8 + mtfg_queue_8_offset) = mtfg_queue_symbol_7; \
        break; \
      } \
    } while (++mtfg_queue_position != 16); \
    if (mtfg_queue_position == 16) { \
      U32 mtfg_queue_symbol_15; \
      increment_mtfg_queue_8(); \
      do { \
        if (symbol_number == *(mtfg_queue_16 + ((mtfg_queue_position + mtfg_queue_16_offset) & 0xF))) { \
          if (in_definition == 0) { \
            EncodeMtfgType(LEVEL0); \
          } \
          else { \
            EncodeMtfgType(LEVEL1); \
          } \
          EncodeMtfgQueuePos(NOT_CAP); \
          if (sd[mtfg_queue_symbol_15].code_length <= 12) { \
            sd[mtfg_queue_symbol_15].type &= 0xF7; \
            remove_mtfg_queue_symbol_16(); \
          } \
          else { \
            subqueue_position = mtfg_queue_position - 16; \
            while (subqueue_position) { \
              *(mtfg_queue_16 + ((mtfg_queue_16_offset + subqueue_position) & 0xF)) \
                  = *(mtfg_queue_16 + ((mtfg_queue_16_offset + subqueue_position - 1) & 0xF)); \
              subqueue_position--; \
            } \
            *(mtfg_queue_16 + mtfg_queue_16_offset) = mtfg_queue_symbol_15; \
          } \
          break; \
        } \
      } while (++mtfg_queue_position != 32); \
      if (mtfg_queue_position == 32) { \
        do { \
          if (symbol_number == *(mtfg_queue_32 + ((mtfg_queue_position + mtfg_queue_32_offset) & 0x1F))) { \
            if (in_definition == 0) { \
              EncodeMtfgType(LEVEL0); \
            } \
            else { \
              EncodeMtfgType(LEVEL1); \
            } \
            EncodeMtfgQueuePos(NOT_CAP); \
            if (sd[mtfg_queue_symbol_15].code_length <= 12) { \
              sd[mtfg_queue_symbol_15].type &= 0xF7; \
              remove_mtfg_queue_symbol_32(); \
            } \
            else { \
              U32 mtfg_queue_symbol_31; \
              increment_mtfg_queue_16(); \
              if (sd[mtfg_queue_symbol_31].code_length == 13) { \
                sd[mtfg_queue_symbol_31].type &= 0xF7; \
                remove_mtfg_queue_symbol_32(); \
              } \
              else { \
                subqueue_position = mtfg_queue_position - 32; \
                while (subqueue_position) { \
                  *(mtfg_queue_32 + ((mtfg_queue_32_offset + subqueue_position) & 0x1F)) \
                      = *(mtfg_queue_32 + ((mtfg_queue_32_offset + subqueue_position - 1) & 0x1F)); \
                  subqueue_position--; \
                } \
                *(mtfg_queue_32 + mtfg_queue_32_offset) = mtfg_queue_symbol_31; \
              } \
            } \
            break; \
          } \
        } while (++mtfg_queue_position != 64); \
        if (mtfg_queue_position == 64) { \
          do { \
            if (symbol_number == *(mtfg_queue_64 + ((mtfg_queue_position + mtfg_queue_64_offset) & 0x3F))) { \
              if (in_definition == 0) { \
                EncodeMtfgType(LEVEL0); \
              } \
              else { \
                EncodeMtfgType(LEVEL1); \
              } \
              EncodeMtfgQueuePos(NOT_CAP); \
              if (sd[mtfg_queue_symbol_15].code_length <= 12) { \
                sd[mtfg_queue_symbol_15].type &= 0xF7; \
                remove_mtfg_queue_symbol_64(); \
              } \
              else { \
                U32 mtfg_queue_symbol_31; \
                increment_mtfg_queue_16(); \
                if (sd[mtfg_queue_symbol_31].code_length == 13) { \
                  sd[mtfg_queue_symbol_31].type &= 0xF7; \
                  remove_mtfg_queue_symbol_64(); \
                } \
                else { \
                  U32 mtfg_queue_symbol_63; \
                  increment_mtfg_queue_32(); \
                  if (sd[mtfg_queue_symbol_63].code_length == 14) { \
                    sd[mtfg_queue_symbol_63].type &= 0xF7; \
                    remove_mtfg_queue_symbol_64(); \
                  } \
                  else { \
                    subqueue_position = mtfg_queue_position - 64; \
                    while (subqueue_position) { \
                      *(mtfg_queue_64 + ((mtfg_queue_64_offset + subqueue_position) & 0x3F)) \
                          = *(mtfg_queue_64 + ((mtfg_queue_64_offset + subqueue_position - 1) & 0x3F)); \
                      subqueue_position--; \
                    } \
                    *(mtfg_queue_64 + mtfg_queue_64_offset) = mtfg_queue_symbol_63; \
                  } \
                } \
              } \
              break; \
            } \
          } while (++mtfg_queue_position != 128); \
          if (mtfg_queue_position == 128) { \
            do { \
              if (symbol_number == *(mtfg_queue_128 + ((mtfg_queue_position + mtfg_queue_128_offset) & 0x3F))) { \
                if (in_definition == 0) { \
                  EncodeMtfgType(LEVEL0); \
                } \
                else { \
                  EncodeMtfgType(LEVEL1); \
                } \
                EncodeMtfgQueuePos(NOT_CAP); \
                if (sd[mtfg_queue_symbol_15].code_length <= 12) { \
                  sd[mtfg_queue_symbol_15].type &= 0xF7; \
                  remove_mtfg_queue_symbol_128(); \
                } \
                else { \
                  U32 mtfg_queue_symbol_31; \
                  increment_mtfg_queue_16(); \
                  if (sd[mtfg_queue_symbol_31].code_length == 13) { \
                    sd[mtfg_queue_symbol_31].type &= 0xF7; \
                    remove_mtfg_queue_symbol_128(); \
                  } \
                  else { \
                    U32 mtfg_queue_symbol_63; \
                    increment_mtfg_queue_32(); \
                    if (sd[mtfg_queue_symbol_63].code_length == 14) { \
                      sd[mtfg_queue_symbol_63].type &= 0xF7; \
                      remove_mtfg_queue_symbol_128(); \
                    } \
                    else { \
                      U32 mtfg_queue_symbol_127; \
                      increment_mtfg_queue_64(); \
                      if (sd[mtfg_queue_symbol_127].code_length == 15) { \
                        sd[mtfg_queue_symbol_127].type &= 0xF7; \
                        remove_mtfg_queue_symbol_128(); \
                      } \
                      else { \
                        subqueue_position = mtfg_queue_position - 128; \
                        while (subqueue_position) { \
                          *(mtfg_queue_128 + ((mtfg_queue_128_offset + subqueue_position) & 0x3F)) \
                              = *(mtfg_queue_128 + ((mtfg_queue_128_offset + subqueue_position - 1) & 0x3F)); \
                          subqueue_position--; \
                        } \
                        *(mtfg_queue_128 + mtfg_queue_128_offset) = mtfg_queue_symbol_127; \
                      } \
                    } \
                  } \
                } \
                break; \
              } \
            } while (++mtfg_queue_position != 192); \
            if (mtfg_queue_position == 192) { \
              while (symbol_number != *(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F))) { \
                if (sd[*(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F))].type & 2) \
                  cap_queue_position++; \
                mtfg_queue_position++; \
              } \
              if (in_definition == 0) { \
                EncodeMtfgType(LEVEL0); \
              } \
              else { \
                EncodeMtfgType(LEVEL1); \
              } \
              EncodeMtfgQueuePos(NOT_CAP); \
              if (sd[mtfg_queue_symbol_15].code_length <= 12) { \
                sd[mtfg_queue_symbol_15].type &= 0xF7; \
                remove_mtfg_queue_symbol_192(); \
              } \
              else { \
                U32 mtfg_queue_symbol_31; \
                increment_mtfg_queue_16(); \
                if (sd[mtfg_queue_symbol_31].code_length == 13) { \
                  sd[mtfg_queue_symbol_31].type &= 0xF7; \
                  remove_mtfg_queue_symbol_192(); \
                } \
                else { \
                  U32 mtfg_queue_symbol_63; \
                  increment_mtfg_queue_32(); \
                  if (sd[mtfg_queue_symbol_63].code_length == 14) { \
                    sd[mtfg_queue_symbol_63].type &= 0xF7; \
                    remove_mtfg_queue_symbol_192(); \
                  } \
                  else { \
                    U32 mtfg_queue_symbol_127; \
                    increment_mtfg_queue_64(); \
                    if (sd[mtfg_queue_symbol_127].code_length == 15) { \
                      sd[mtfg_queue_symbol_127].type &= 0xF7; \
                      remove_mtfg_queue_symbol_192(); \
                    } \
                    else { \
                      U32 mtfg_queue_symbol_191; \
                      increment_mtfg_queue_128(); \
                      if (sd[mtfg_queue_symbol_191].code_length == 16) { \
                        sd[mtfg_queue_symbol_191].type &= 0xF7; \
                        remove_mtfg_queue_symbol_192(); \
                      } \
                      else { \
                        subqueue_position = mtfg_queue_position - 192; \
                        while (subqueue_position) { \
                          *(mtfg_queue_192 + ((mtfg_queue_192_offset + subqueue_position) & 0x3F)) \
                              = *(mtfg_queue_192 + ((mtfg_queue_192_offset + subqueue_position - 1) & 0x3F)); \
                          subqueue_position--; \
                        } \
                        *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191; \
} } } } } } } } } } } } \


#define manage_mtfg_queue_prior_cap(symbol_number, in_definition) { \
  U8 mtfg_queue_position = 0; \
  U8 cap_queue_position = 0; \
  U8 subqueue_position; \
  do { \
    if (symbol_number == mtfg_queue_0[mtfg_queue_position]) { \
      if (in_definition == 0) { \
        EncodeMtfgType(LEVEL0_CAP); \
      } \
      else { \
        EncodeMtfgType(LEVEL1_CAP); \
      } \
      U8 saved_qp = mtfg_queue_position; \
      mtfg_queue_position = cap_queue_position; \
      EncodeMtfgQueuePos(CAP); \
      mtfg_queue_position = saved_qp; \
      while (mtfg_queue_position) { \
        mtfg_queue_0[mtfg_queue_position] = mtfg_queue_0[mtfg_queue_position-1]; \
        mtfg_queue_position--; \
      } \
      mtfg_queue_0[0] = symbol_number; \
      break; \
    } \
    else if (sd[mtfg_queue_0[mtfg_queue_position]].type & 2) \
      cap_queue_position++; \
  } while (++mtfg_queue_position != 8); \
  if (mtfg_queue_position == 8) { \
    U32 mtfg_queue_symbol_7; \
    increment_mtfg_queue_0(symbol_number); \
    do { \
      if (symbol_number == *(mtfg_queue_8 + ((mtfg_queue_position + mtfg_queue_8_offset) & 7))) { \
        if (in_definition == 0) { \
          EncodeMtfgType(LEVEL0_CAP); \
        } \
        else { \
          EncodeMtfgType(LEVEL1_CAP); \
        } \
        U8 saved_qp = mtfg_queue_position; \
        mtfg_queue_position = cap_queue_position; \
        EncodeMtfgQueuePos(CAP); \
        mtfg_queue_position = saved_qp; \
        subqueue_position = mtfg_queue_position - 8; \
        while (subqueue_position) { \
          *(mtfg_queue_8 + ((mtfg_queue_8_offset + subqueue_position) & 7)) \
              = *(mtfg_queue_8 + ((mtfg_queue_8_offset + subqueue_position - 1) & 7)); \
          subqueue_position--; \
        } \
        *(mtfg_queue_8 + mtfg_queue_8_offset) = mtfg_queue_symbol_7; \
        break; \
      } \
      else if (sd[*(mtfg_queue_8 + ((mtfg_queue_position + mtfg_queue_8_offset) & 7))].type & 2) \
        cap_queue_position++; \
    } while (++mtfg_queue_position != 16); \
    if (mtfg_queue_position == 16) { \
      U32 mtfg_queue_symbol_15; \
      increment_mtfg_queue_8(); \
      do { \
        if (symbol_number == *(mtfg_queue_16 + ((mtfg_queue_position + mtfg_queue_16_offset) & 0xF))) { \
          if (in_definition == 0) { \
            EncodeMtfgType(LEVEL0_CAP); \
          } \
          else { \
            EncodeMtfgType(LEVEL1_CAP); \
          } \
          U8 saved_qp = mtfg_queue_position; \
          mtfg_queue_position = cap_queue_position; \
          EncodeMtfgQueuePos(CAP); \
          mtfg_queue_position = saved_qp; \
          if (sd[mtfg_queue_symbol_15].code_length <= 12) { \
            sd[mtfg_queue_symbol_15].type &= 0xF7; \
            remove_mtfg_queue_symbol_16(); \
          } \
          else { \
            subqueue_position = mtfg_queue_position - 16; \
            while (subqueue_position) { \
              *(mtfg_queue_16 + ((mtfg_queue_16_offset + subqueue_position) & 0xF)) \
                  = *(mtfg_queue_16 + ((mtfg_queue_16_offset + subqueue_position - 1) & 0xF)); \
              subqueue_position--; \
            } \
            *(mtfg_queue_16 + mtfg_queue_16_offset) = mtfg_queue_symbol_15; \
          } \
          break; \
        } \
        else if (sd[*(mtfg_queue_16 + ((mtfg_queue_position + mtfg_queue_16_offset) & 0xF))].type & 2) \
          cap_queue_position++; \
      } while (++mtfg_queue_position != 32); \
      if (mtfg_queue_position == 32) { \
        do { \
          if (symbol_number == *(mtfg_queue_32 + ((mtfg_queue_position + mtfg_queue_32_offset) & 0x1F))) { \
            if (in_definition == 0) { \
              EncodeMtfgType(LEVEL0_CAP); \
            } \
            else { \
              EncodeMtfgType(LEVEL1_CAP); \
            } \
            U8 saved_qp = mtfg_queue_position; \
            mtfg_queue_position = cap_queue_position; \
            EncodeMtfgQueuePos(CAP); \
            mtfg_queue_position = saved_qp; \
            if (sd[mtfg_queue_symbol_15].code_length <= 12) { \
              sd[mtfg_queue_symbol_15].type &= 0xF7; \
              remove_mtfg_queue_symbol_32(); \
            } \
            else { \
              U32 mtfg_queue_symbol_31; \
              increment_mtfg_queue_16(); \
              if (sd[mtfg_queue_symbol_31].code_length == 13) { \
                sd[mtfg_queue_symbol_31].type &= 0xF7; \
                remove_mtfg_queue_symbol_32(); \
              } \
              else { \
                subqueue_position = mtfg_queue_position - 32; \
                while (subqueue_position) { \
                  *(mtfg_queue_32 + ((mtfg_queue_32_offset + subqueue_position) & 0x1F)) \
                      = *(mtfg_queue_32 + ((mtfg_queue_32_offset + subqueue_position - 1) & 0x1F)); \
                  subqueue_position--; \
                } \
                *(mtfg_queue_32 + mtfg_queue_32_offset) = mtfg_queue_symbol_31; \
              } \
            } \
            break; \
          } \
          else if (sd[*(mtfg_queue_32 + ((mtfg_queue_position + mtfg_queue_32_offset) & 0x1F))].type & 2) \
            cap_queue_position++; \
        } while (++mtfg_queue_position != 64); \
        if (mtfg_queue_position == 64) { \
          do { \
            if (symbol_number == *(mtfg_queue_64 + ((mtfg_queue_position + mtfg_queue_64_offset) & 0x3F))) { \
              if (in_definition == 0) { \
                EncodeMtfgType(LEVEL0_CAP); \
              } \
              else { \
                EncodeMtfgType(LEVEL1_CAP); \
              } \
              U8 saved_qp = mtfg_queue_position; \
              mtfg_queue_position = cap_queue_position; \
              EncodeMtfgQueuePos(CAP); \
              mtfg_queue_position = saved_qp; \
              if (sd[mtfg_queue_symbol_15].code_length <= 12) { \
                sd[mtfg_queue_symbol_15].type &= 0xF7; \
                remove_mtfg_queue_symbol_64(); \
              } \
              else { \
                U32 mtfg_queue_symbol_31; \
                increment_mtfg_queue_16(); \
                if (sd[mtfg_queue_symbol_31].code_length == 13) { \
                  sd[mtfg_queue_symbol_31].type &= 0xF7; \
                  remove_mtfg_queue_symbol_64(); \
                } \
                else { \
                  U32 mtfg_queue_symbol_63; \
                  increment_mtfg_queue_32(); \
                  if (sd[mtfg_queue_symbol_63].code_length == 14) { \
                    sd[mtfg_queue_symbol_63].type &= 0xF7; \
                    remove_mtfg_queue_symbol_64(); \
                  } \
                  else { \
                    subqueue_position = mtfg_queue_position - 64; \
                    while (subqueue_position) { \
                      *(mtfg_queue_64 + ((mtfg_queue_64_offset + subqueue_position) & 0x3F)) \
                          = *(mtfg_queue_64 + ((mtfg_queue_64_offset + subqueue_position - 1) & 0x3F)); \
                      subqueue_position--; \
                    } \
                    *(mtfg_queue_64 + mtfg_queue_64_offset) = mtfg_queue_symbol_63; \
                  } \
                } \
              } \
              break; \
            } \
            else if (sd[*(mtfg_queue_64 + ((mtfg_queue_position + mtfg_queue_64_offset) & 0x3F))].type & 2) \
              cap_queue_position++; \
          } while (++mtfg_queue_position != 128); \
          if (mtfg_queue_position == 128) { \
            do { \
              if (symbol_number == *(mtfg_queue_128 + ((mtfg_queue_position + mtfg_queue_128_offset) & 0x3F))) { \
                if (in_definition == 0) { \
                  EncodeMtfgType(LEVEL0_CAP); \
                } \
                else { \
                  EncodeMtfgType(LEVEL1_CAP); \
                } \
                U8 saved_qp = mtfg_queue_position; \
                mtfg_queue_position = cap_queue_position; \
                EncodeMtfgQueuePos(CAP); \
                mtfg_queue_position = saved_qp; \
                if (sd[mtfg_queue_symbol_15].code_length <= 12) { \
                  sd[mtfg_queue_symbol_15].type &= 0xF7; \
                  remove_mtfg_queue_symbol_128(); \
                } \
                else { \
                  U32 mtfg_queue_symbol_31; \
                  increment_mtfg_queue_16(); \
                  if (sd[mtfg_queue_symbol_31].code_length == 13) { \
                    sd[mtfg_queue_symbol_31].type &= 0xF7; \
                    remove_mtfg_queue_symbol_128(); \
                  } \
                  else { \
                    U32 mtfg_queue_symbol_63; \
                    increment_mtfg_queue_32(); \
                    if (sd[mtfg_queue_symbol_63].code_length == 14) { \
                      sd[mtfg_queue_symbol_63].type &= 0xF7; \
                      remove_mtfg_queue_symbol_128(); \
                    } \
                    else { \
                      U32 mtfg_queue_symbol_127; \
                      increment_mtfg_queue_64(); \
                      if (sd[mtfg_queue_symbol_127].code_length == 15) { \
                        sd[mtfg_queue_symbol_127].type &= 0xF7; \
                        remove_mtfg_queue_symbol_128(); \
                      } \
                      else { \
                        subqueue_position = mtfg_queue_position - 128; \
                        while (subqueue_position) { \
                          *(mtfg_queue_128 + ((mtfg_queue_128_offset + subqueue_position) & 0x3F)) \
                              = *(mtfg_queue_128 + ((mtfg_queue_128_offset + subqueue_position - 1) & 0x3F)); \
                          subqueue_position--; \
                        } \
                        *(mtfg_queue_128 + mtfg_queue_128_offset) = mtfg_queue_symbol_127; \
                      } \
                    } \
                  } \
                } \
                break; \
              } \
              else if (sd[*(mtfg_queue_128 + ((mtfg_queue_position + mtfg_queue_128_offset) & 0x3F))].type & 2) \
                cap_queue_position++; \
            } while (++mtfg_queue_position != 192); \
            if (mtfg_queue_position == 192) { \
              while (symbol_number != *(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F))) { \
                if (sd[*(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F))].type & 2) \
                  cap_queue_position++; \
                mtfg_queue_position++; \
              } \
              if (in_definition == 0) { \
                EncodeMtfgType(LEVEL0_CAP); \
              } \
              else { \
                EncodeMtfgType(LEVEL1_CAP); \
              } \
              U8 saved_qp = mtfg_queue_position; \
              mtfg_queue_position = cap_queue_position; \
              EncodeMtfgQueuePos(CAP); \
              mtfg_queue_position = saved_qp; \
              if (sd[mtfg_queue_symbol_15].code_length <= 12) { \
                sd[mtfg_queue_symbol_15].type &= 0xF7; \
                remove_mtfg_queue_symbol_192(); \
              } \
              else { \
                U32 mtfg_queue_symbol_31; \
                increment_mtfg_queue_16(); \
                if (sd[mtfg_queue_symbol_31].code_length == 13) { \
                  sd[mtfg_queue_symbol_31].type &= 0xF7; \
                  remove_mtfg_queue_symbol_192(); \
                } \
                else { \
                  U32 mtfg_queue_symbol_63; \
                  increment_mtfg_queue_32(); \
                  if (sd[mtfg_queue_symbol_63].code_length == 14) { \
                    sd[mtfg_queue_symbol_63].type &= 0xF7; \
                    remove_mtfg_queue_symbol_192(); \
                  } \
                  else { \
                    U32 mtfg_queue_symbol_127; \
                    increment_mtfg_queue_64(); \
                    if (sd[mtfg_queue_symbol_127].code_length == 15) { \
                      sd[mtfg_queue_symbol_127].type &= 0xF7; \
                      remove_mtfg_queue_symbol_192(); \
                    } \
                    else { \
                      U32 mtfg_queue_symbol_191; \
                      increment_mtfg_queue_128(); \
                      if (sd[mtfg_queue_symbol_191].code_length == 16) { \
                        sd[mtfg_queue_symbol_191].type &= 0xF7; \
                        remove_mtfg_queue_symbol_192(); \
                      } \
                      else { \
                        subqueue_position = mtfg_queue_position - 192; \
                        while (subqueue_position) { \
                          *(mtfg_queue_192 + ((mtfg_queue_192_offset + subqueue_position) & 0x3F)) \
                              = *(mtfg_queue_192 + ((mtfg_queue_192_offset + subqueue_position - 1) & 0x3F)); \
                          subqueue_position--; \
                        } \
                        *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191; \
} } } } } } } } } } } } \


inline void encode_dictionary_symbol(U32 dsymbol) {
  symbol_index = sd[dsymbol].array_index;
  Symbol = sd[dsymbol].starts;
  if (cap_encoded) {
    if (prior_end != 0xA) {
      if (max_code_length >= 14) {
        if (sd[prior_symbol].type & 0x20) {
          if (sd[prior_symbol].type & 0x80) {
            EncodeFirstChar(2, prior_end);
          }
          else if (sd[prior_symbol].type & 0x40) {
            EncodeFirstChar(3, prior_end);
          }
          else {
            EncodeFirstChar(1, prior_end);
          }
        }
        else {
          EncodeFirstChar(0, prior_end);
        }
      }
      else {
        EncodeFirstChar(0, prior_end);
      }
    }
  }
  else if (UTF8_compliant) {
    EncodeFirstChar(0, prior_end);
  }
  else {
    EncodeFirstCharBinary(prior_end);
  }
  DictionaryBins = sum_nbob[Symbol];
  if (CodeLength > 12 + nbob_shift[Symbol]) {
    U32 max_codes_in_bins, mcib;
    U8 reduce_bits = 0;
    max_codes_in_bins = nbob[Symbol][CodeLength] << (CodeLength - (12 + nbob_shift[Symbol]));
    mcib = max_codes_in_bins >> 1;
    while (mcib >= nsob[Symbol][CodeLength]) {
      reduce_bits++;
      mcib = mcib >> 1;
    }
    if (CodeLength - reduce_bits > 12 + nbob_shift[Symbol]) {
      BinNum = fbob[Symbol][CodeLength];
      min_extra_reduce_index = 2 * nsob[Symbol][CodeLength] - (max_codes_in_bins >> reduce_bits);
      if (symbol_index >= min_extra_reduce_index) {
        U16 symbol_bins = 2;
        BinCode = 2 * symbol_index - min_extra_reduce_index;
        U16 code_bin = (U16)(BinCode >> (CodeLength - (12 + nbob_shift[Symbol]) - reduce_bits));
        BinNum += code_bin;
        BinCode -= (U32)code_bin << (CodeLength - (12 + nbob_shift[Symbol]) - reduce_bits);
        while (BinCode && (sd[sym_list_ptrs[Symbol][CodeLength][--symbol_index]].type & 8)) {
          if (symbol_index >= min_extra_reduce_index) {
            symbol_bins += 2;
            BinCode -= 2;
          }
          else {
            symbol_bins++;
            BinCode--;
          }
        }
        CodeLength -= reduce_bits + nbob_shift[Symbol];
        EncodeLongDictionarySymbol(symbol_bins);
      }
      else {
        BinCode = symbol_index;
        U16 symbol_bins = 1;
        while ((BinCode & ((1 << (CodeLength - (12 + nbob_shift[Symbol]) - reduce_bits)) - 1))
            && (sd[sym_list_ptrs[Symbol][CodeLength][BinCode - 1]].type & 8)) {
          symbol_bins++;
          BinCode--;
        }
        CodeLength -= reduce_bits + nbob_shift[Symbol];
        U16 code_bin = (U16)(symbol_index >> (CodeLength - 12));
        BinNum += code_bin;
        BinCode -= (U32)code_bin << (CodeLength - 12);
        EncodeLongDictionarySymbol(symbol_bins);
      }
    }
    else {
      U16 symbol_bins = 1;
      while (symbol_index && (sd[sym_list_ptrs[Symbol][CodeLength][symbol_index - 1]].type & 8)) {
        symbol_bins++;
        symbol_index--;
      }
      BinNum = fbob[Symbol][CodeLength] + symbol_index;
      EncodeShortDictionarySymbol(12, symbol_bins);
    }
  }
  else {
    U16 symbol_bins = 1;
    while (symbol_index && (sd[sym_list_ptrs[Symbol][CodeLength][symbol_index - 1]].type & 8)) {
      symbol_bins++;
      symbol_index--;
    }
    BinNum = fbob[Symbol][CodeLength] + (symbol_index << (12 + nbob_shift[Symbol] - CodeLength));
    EncodeShortDictionarySymbol(CodeLength - nbob_shift[Symbol], symbol_bins);
  }
  return;
}


inline void update_mtf_queue(U32 this_symbol, U32 symbol_inst, U32 this_symbol_count) {
  U32 i1;
  if (symbol_inst != this_symbol_count - 1) { // not the last instance
    if (sd[this_symbol].type & 8) { // symbol in queue
      i1 = mtf_queue_size[this_symbol_count] - 1;
      while (mtf_queue[this_symbol_count][i1] != this_symbol)
        i1--;
      mtf_queue_hit_count[this_symbol_count][mtf_queue_size[this_symbol_count] - i1]++;
      while (i1 < mtf_queue_size[this_symbol_count] - 1) {
        mtf_queue[this_symbol_count][i1] = mtf_queue[this_symbol_count][i1+1];
        i1++;
      }
      mtf_queue[this_symbol_count][i1] = this_symbol;
    }
    else { // symbol not in mtf queue, move it back into the queue
      sd[this_symbol].type |= 8;
      if (mtf_queue_size[this_symbol_count] < MTF_QUEUE_SIZE)
        mtf_queue[this_symbol_count][mtf_queue_size[this_symbol_count]++] = this_symbol;
      else { // move the queue elements down
        sd[mtf_queue[this_symbol_count][0]].type &= 0xF7;
        i1 = 0;
        while (i1 < mtf_queue_size[this_symbol_count] - 1) {
          mtf_queue[this_symbol_count][i1] = mtf_queue[this_symbol_count][i1+1];
          i1++;
        }
        mtf_queue[this_symbol_count][i1] = this_symbol;
      }
    }
  }
  else { // last instance
    mtf_queue_done[this_symbol_count]++;
    if (sd[this_symbol].type & 8) {
      i1 = mtf_queue_size[this_symbol_count] - 1;
      while (mtf_queue[this_symbol_count][i1] != this_symbol)
        i1--;
      mtf_queue_hit_count[this_symbol_count][(mtf_queue_size[this_symbol_count]--) - i1]++;
      while (i1 < mtf_queue_size[this_symbol_count]) {
        mtf_queue[this_symbol_count][i1] = mtf_queue[this_symbol_count][i1+1];
        i1++;
      }
    }
  }
  return;
}


#define add_dictionary_symbol(symbol, bits) { \
  U8 first_char = sd[symbol].starts; \
  if (nsob[first_char][bits] == (1 << sym_list_bits[first_char][bits])) { \
    sym_list_bits[first_char][bits]++; \
    if (0 == (sym_list_ptrs[first_char][bits] \
        = (U32 *)realloc(sym_list_ptrs[first_char][bits], sizeof(U32) * (1 << sym_list_bits[first_char][bits])))) { \
      fprintf(stderr,"FATAL ERROR - symbol list realloc failure\n"); \
      exit(0); \
    } \
  } \
  sd[symbol].array_index = nsob[first_char][bits]; \
  sym_list_ptrs[first_char][bits][nsob[first_char][bits]++] = symbol; \
  if ((nsob[first_char][bits] << (32 - bits)) > (nbob[first_char][bits] << (20 - nbob_shift[first_char]))) { \
    if (bits >= 12 + nbob_shift[first_char]) { \
      nbob[first_char][bits]++; \
      sum_nbob[first_char]++; \
      for (temp_bits = bits + 1 ; temp_bits <= max_code_length ; temp_bits++) \
        fbob[first_char][temp_bits]++; \
    } \
    else { \
      nbob[first_char][bits] += 1 << (12 + nbob_shift[first_char] - bits); \
      sum_nbob[first_char] += 1 << (12 + nbob_shift[first_char] - bits); \
      for (temp_bits = bits + 1 ; temp_bits <= max_code_length ; temp_bits++) \
        fbob[first_char][temp_bits] += 1 << (12 + nbob_shift[first_char] - bits); \
    } \
    if (sum_nbob[first_char] > 0x1000) { \
      do { \
        nbob_shift[first_char]--; \
        U8 code_length; \
        sum_nbob[first_char] = 0; \
        for (code_length = 1 ; code_length <= max_code_length ; code_length++) \
          sum_nbob[first_char] += (nbob[first_char][code_length] = (nbob[first_char][code_length] + 1) >> 1); \
      } while (sum_nbob[first_char] > 0x1000); \
      U16 bin = nbob[first_char][1]; \
      for (temp_bits = 2 ; temp_bits <= max_code_length ; temp_bits++) { \
        fbob[first_char][temp_bits] = bin; \
        bin += nbob[first_char][temp_bits]; \
      } \
    } \
  } \
}


#define remove_dictionary_symbol(symbol, bits) { \
  U8 first_char = sd[symbol].starts; \
  sym_list_ptrs[first_char][bits][sd[symbol].array_index] = sym_list_ptrs[first_char][bits][--nsob[first_char][bits]]; \
  sd[sym_list_ptrs[first_char][bits][nsob[first_char][bits]]].array_index = sd[symbol].array_index; \
}


inline void manage_mtf_queue(U32 this_symbol, U32 symbol_inst, U32 this_symbol_count, U8 in_definition) {
  U32 i1, mtf_queue_position;
  mtf_queue_number = (U8)this_symbol_count - 2;
  if (symbol_inst != this_symbol_count - 1) { // not the last instance
    if (sd[this_symbol].type & 8) {
      i1 = mtf_queue_size[this_symbol_count];
      while (i1 != 0) {
        i1--;
        if (mtf_queue[this_symbol_count][i1] == this_symbol) { // return the instance hit code and instance hit code bits
          mtf_queue_position = mtf_queue_size[this_symbol_count] - i1 - 1;
          if (prior_is_cap == 0) {
            if (in_definition == 0) {
              EncodeMtfType(LEVEL0);
            }
            else {
              EncodeMtfType(LEVEL1);
            }
            EncodeMtfQueueNum(NOT_CAP);
            EncodeMtfQueuePos(NOT_CAP);
          }
          else {
            if (in_definition == 0) {
              EncodeMtfType(LEVEL0_CAP);
            }
            else {
              EncodeMtfType(LEVEL1_CAP);
            }
            EncodeMtfQueueNum(CAP);
            if (mtf_queue_position) {
              U32 *end_mtf_queue_ptr = &mtf_queue[this_symbol_count][mtf_queue_size[this_symbol_count] - 1];
              U32 *mtf_queue_ptr = end_mtf_queue_ptr - mtf_queue_position + 1;
              do {
                if ((sd[*mtf_queue_ptr].type & 2) == 0)
                  mtf_queue_position--;
              } while (mtf_queue_ptr++ != end_mtf_queue_ptr);
            }
            EncodeMtfQueuePos(CAP);
          }
          while (i1 < mtf_queue_size[this_symbol_count] - 1) {
            mtf_queue[this_symbol_count][i1] = mtf_queue[this_symbol_count][i1+1];
            i1++;
          }
          mtf_queue[this_symbol_count][i1] = this_symbol;
          prior_is_cap = cap_encoded & sd[this_symbol].type;
          return;
        }
      }
    }
    // symbol not in mtf queue, return the symbol code and length
    sd[this_symbol].type |= 8;
    CodeLength = sd[this_symbol].code_length;
    if (prior_is_cap == 0) {
      UpFreqMtfQueueNum(NOT_CAP);
      if (in_definition == 0) {
        EncodeDictType(LEVEL0);
      }
      else {
        EncodeDictType(LEVEL1);
      }
    }
    else {
      UpFreqMtfQueueNum(CAP);
      if (in_definition == 0) {
        EncodeDictType(LEVEL0_CAP);
      }
      else {
        EncodeDictType(LEVEL1_CAP);
      }
    }
    encode_dictionary_symbol(this_symbol);
    // move the symbol back into the mtf queue
    symbol_bits = mtf_queue_overflow_code_length[this_symbol_count];
    if (mtf_queue_size[this_symbol_count] < MTF_QUEUE_SIZE) {
      mtf_queue[this_symbol_count][mtf_queue_size[this_symbol_count]++] = this_symbol;
      remove_dictionary_symbol(this_symbol, symbol_bits);
    }
    else {
      sd[mtf_queue[this_symbol_count][0]].type &= 0xF7;
      symbol_to_move = mtf_queue[this_symbol_count][0];
      remove_dictionary_symbol(this_symbol, symbol_bits);
      add_dictionary_symbol(symbol_to_move, symbol_bits);
      // move the queue elements down
      while (i1 < mtf_queue_size[this_symbol_count] - 1) {
        mtf_queue[this_symbol_count][i1] = mtf_queue[this_symbol_count][i1+1];
        i1++;
      }
      mtf_queue[this_symbol_count][i1] = this_symbol;
    }
    prior_is_cap = cap_encoded & sd[this_symbol].type;
  }
  else { // last instance
    // default is to return the symbol code and length if no match found
    if (sd[this_symbol].type & 8) {
      i1 = mtf_queue_size[this_symbol_count];
      while (i1-- != 0) {
        if (mtf_queue[this_symbol_count][i1] == this_symbol) { // return the mtf queue code and length
          mtf_queue_position = mtf_queue_size[this_symbol_count] - i1 - 1;
          if (prior_is_cap == 0) {
            if (in_definition == 0) {
              EncodeMtfType(LEVEL0);
            }
            else {
              EncodeMtfType(LEVEL1);
            }
            EncodeMtfQueueNumLastSymbol(NOT_CAP);
            EncodeMtfQueuePos(NOT_CAP);
          }
          else {
            if (in_definition == 0) {
              EncodeMtfType(LEVEL0_CAP);
            }
            else {
              EncodeMtfType(LEVEL1_CAP);
            }
            EncodeMtfQueueNumLastSymbol(CAP);
            if (mtf_queue_position) {
              U32 *end_mtf_queue_ptr = &mtf_queue[this_symbol_count][mtf_queue_size[this_symbol_count] - 1];
              U32 *mtf_queue_ptr = end_mtf_queue_ptr - mtf_queue_position + 1;
              do {
                if ((sd[*mtf_queue_ptr].type & 2) == 0)
                  mtf_queue_position--;
              } while (mtf_queue_ptr++ != end_mtf_queue_ptr);
            }
            EncodeMtfQueuePos(CAP);
          }
          mtf_queue_size[this_symbol_count]--;
          mtf_queue_ptr = &mtf_queue[this_symbol_count][i1];
          mtf_queue_end_ptr = &mtf_queue[this_symbol_count][mtf_queue_size[this_symbol_count]];
          while (mtf_queue_ptr != mtf_queue_end_ptr)
          {
            *mtf_queue_ptr = *(mtf_queue_ptr+1);
            mtf_queue_ptr++;
          }
          prior_is_cap = cap_encoded & sd[this_symbol].type;
          return;
        }
      }
    }
    // symbol not in mtf queue, return the symbol code and length
    CodeLength = sd[this_symbol].code_length;
    if (prior_is_cap == 0) {
      if (in_definition == 0) {
        EncodeDictType(LEVEL0);
      }
      else {
        EncodeDictType(LEVEL1);
      }
    }
    else {
      if (in_definition == 0) {
        EncodeDictType(LEVEL0_CAP);
      }
      else {
        EncodeDictType(LEVEL1_CAP);
      }
    }
    encode_dictionary_symbol(this_symbol);
    symbol_bits = mtf_queue_overflow_code_length[this_symbol_count];
    remove_dictionary_symbol(this_symbol, symbol_bits);
    prior_is_cap = cap_encoded & sd[this_symbol].type;
  }
  return;
}


inline void manage_mtf_symbol(U32 this_symbol, U32 symbol_inst, U32 this_symbol_count, U8 in_definition) {
  CodeLength = sd[this_symbol].code_length;
  if (prior_is_cap == 0) {
    if (in_definition == 0) {
      EncodeDictType(LEVEL0);
    }
    else {
      EncodeDictType(LEVEL1);
    }
  }
  else {
    if (in_definition == 0) {
      EncodeDictType(LEVEL0_CAP);
    }
    else {
      EncodeDictType(LEVEL1_CAP);
    }
  }
  encode_dictionary_symbol(this_symbol);
  prior_is_cap = cap_encoded & sd[this_symbol].type;
  if (symbol_inst == this_symbol_count - 1) { // last instance
    symbol_bits = mtf_queue_overflow_code_length[this_symbol_count];
    remove_dictionary_symbol(this_symbol, symbol_bits);
  }
  return;
}


inline U32 count_symbols(U32 this_symbol) {
  U32 string_symbols, *symbol_string_ptr, *end_symbol_string_ptr;
  if (this_symbol < start_my_symbols)
    return(1);
  symbol_string_ptr = symbol + sd[this_symbol].define_symbol_start_index;
  end_symbol_string_ptr = symbol + sd[this_symbol+1].define_symbol_start_index - 1;

  string_symbols = 0;
  while (symbol_string_ptr != end_symbol_string_ptr) {
    if ((sd[*symbol_string_ptr].count == 1) && (*symbol_string_ptr >= start_my_symbols))
      string_symbols += count_symbols(*symbol_string_ptr);
    else
      string_symbols++;
    symbol_string_ptr++;
  }
  return(string_symbols);
}


void count_embedded_definition_symbols(U32 define_symbol) {
  U32 *define_string_ptr, *define_string_end_ptr;
  U32 define_symbol_instances, symbol_inst, i1, this_symbol, this_symbol_count;

  if ((sd[define_symbol].count == 1) && (define_symbol >= start_my_symbols)) {
    // count the symbols in the string instead of creating a single instance symbol (artifacts of TreeCompress)
    define_string_ptr = symbol + sd[define_symbol].define_symbol_start_index;
    define_string_end_ptr = symbol + sd[define_symbol+1].define_symbol_start_index - 1;
    do {
      this_symbol = *define_string_ptr++;
      if (define_string_ptr != symbol + sd[define_symbol].define_symbol_start_index) {
        if (sd[prior_symbol].type & 0x20) {
          if (sd[this_symbol].starts == 0x20)
            sd[prior_symbol].space_score += 2;
          else
            sd[prior_symbol].space_score -= 9;
        }
      }
      symbol_inst = sd[this_symbol].inst_found++;
      define_symbol_instances = sd[this_symbol].count;
      if (symbol_inst == 0)
        count_embedded_definition_symbols(this_symbol);
      else if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE) {
        update_mtf_queue(this_symbol,symbol_inst,define_symbol_instances);
        prior_symbol = this_symbol;
      }
      else {
        CodeLength = sd[this_symbol].code_length;
        if (CodeLength >= 11) {
          if (sd[this_symbol].type & 8) {
            manage_mtfg_queue1(this_symbol);
            sd[this_symbol].mtfg_hits++;
          }
          else {
            add_symbol_to_mtfg_queue(this_symbol);
          }
        }
        prior_symbol = this_symbol;
      }
    } while (define_string_ptr != define_string_end_ptr);
    define_string_ptr--;
    sd[define_symbol].type |= sd[this_symbol].type & 0x30;
    while (((sd[define_symbol].type & 0x10) == 0)
        && (define_string_ptr-- != symbol + sd[define_symbol].define_symbol_start_index))
      get_symbol_category(*define_string_ptr, &sd[define_symbol].type);
    return;
  }

  // get the symbol code length
  define_symbol_instances = sd[define_symbol].count;
  if (define_symbol_instances != 1) { // calculate the new code
    if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE)
      symbol_code_length = mtf_queue_overflow_code_length[define_symbol_instances];
    else
      symbol_code_length = sd[define_symbol].code_length;
  }

  // count the symbols in the definition
  if (define_symbol >= start_my_symbols) {
    define_string_ptr = symbol + sd[define_symbol].define_symbol_start_index;
    define_string_end_ptr = symbol + sd[define_symbol+1].define_symbol_start_index - 1;
    do {
      this_symbol = *define_string_ptr;
      if (define_string_ptr != symbol + sd[define_symbol].define_symbol_start_index) {
        if (sd[prior_symbol].type & 0x20) {
          if (sd[this_symbol].starts == 0x20)
            sd[prior_symbol].space_score += 2;
          else
            sd[prior_symbol].space_score -= 9;
        }
      }
      define_string_ptr++;
      symbol_inst = sd[this_symbol].inst_found++;
      this_symbol_count = sd[this_symbol].count;
      if (symbol_inst == 0)
        count_embedded_definition_symbols(this_symbol);
      else if (this_symbol_count <= MAX_INSTANCES_FOR_MTF_QUEUE) {
        update_mtf_queue(this_symbol,symbol_inst,this_symbol_count);
        prior_symbol = this_symbol;
      }
      else {
        CodeLength = sd[this_symbol].code_length;
        if (CodeLength >= 11) {
          if (sd[this_symbol].type & 8) {
            manage_mtfg_queue1(this_symbol);
            sd[this_symbol].mtfg_hits++;
          }
          else {
            add_symbol_to_mtfg_queue(this_symbol);
          }
        }
        prior_symbol = this_symbol;
      }
    } while (define_string_ptr != define_string_end_ptr);
    define_string_ptr--;
    sd[define_symbol].type |= sd[this_symbol].type & 0x30;
    while (((sd[define_symbol].type & 0x10) == 0)
        && (define_string_ptr-- != symbol + sd[define_symbol].define_symbol_start_index))
      get_symbol_category(*define_string_ptr, &sd[define_symbol].type);
  }
  else if ((define_symbol == (U32)' ') || (define_symbol == (U32)'C') || (define_symbol == (U32)'B')) {
    sd[define_symbol].type |= 0x10;
  }
  prior_symbol = define_symbol;

  if (define_symbol_instances != 1) { // assign symbol code
    if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE) { // Handle initial mtf instance
      sd[define_symbol].type |= 8;
      mtf_queue_started[define_symbol_instances]++;
      if (mtf_queue_started[define_symbol_instances] - mtf_queue_done[define_symbol_instances]
          > mtf_queue_peak[define_symbol_instances])
        mtf_queue_peak[define_symbol_instances]++;
      if (mtf_queue_size[define_symbol_instances] < MTF_QUEUE_SIZE)
        mtf_queue[define_symbol_instances][mtf_queue_size[define_symbol_instances]++] = define_symbol;
      else {
        sd[mtf_queue[define_symbol_instances][0]].type &= 0xF7;
        for (i1=0 ; i1<63 ; i1++)
          mtf_queue[define_symbol_instances][i1] = mtf_queue[define_symbol_instances][i1+1];
        mtf_queue[define_symbol_instances][63] = define_symbol;
      }
    }
    else {
      sd[define_symbol].mtfg_hits = 0;
      sd[define_symbol].hit_score = 0;
      CodeLength = sd[define_symbol].code_length;
      if (CodeLength >= 11) {
        add_symbol_to_mtfg_queue(define_symbol);
      }
    }
  }
  num_define_symbols_written++;
  return;
}


void embed_define_binary(U32 define_symbol, U8 in_definition) {
  U32 *define_string_ptr, *this_define_symbol_start_ptr, *define_string_end_ptr;
  U32 define_symbol_instances, symbols_in_definition, symbol_inst, i1, this_symbol, this_symbol_count;
  U8 new_symbol_code_length;

  if ((sd[define_symbol].count == 1) && (define_symbol >= start_my_symbols)) {
    // write the symbol string instead of creating a single instance symbol (artifacts of TreeCompress)
    rules_reduced++;
    define_string_ptr = symbol + sd[define_symbol].define_symbol_start_index;
    define_string_end_ptr = symbol + sd[define_symbol+1].define_symbol_start_index - 1;
    while (define_string_ptr != define_string_end_ptr) {
      this_symbol = *define_string_ptr++;
      symbol_inst = sd[this_symbol].inst_found++;
      define_symbol_instances = sd[this_symbol].count;
      if (symbol_inst == 0)
        embed_define_binary(this_symbol, in_definition);
      else if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE) {
        if (use_mtf) {
          manage_mtf_queue(this_symbol,symbol_inst,define_symbol_instances,in_definition);
        }
        else {
          manage_mtf_symbol(this_symbol,symbol_inst,define_symbol_instances,in_definition);
        }
      }
      else {
        if (sd[this_symbol].type & 8) {
          if (prior_is_cap == 0) {
            manage_mtfg_queue(this_symbol,in_definition);
          }
          else {
            manage_mtfg_queue_prior_cap(this_symbol,in_definition);
          }
        }
        else {
          CodeLength = sd[this_symbol].code_length;
          if (in_definition == 0) {
            EncodeDictType(LEVEL0);
          }
          else {
            EncodeDictType(LEVEL1);
          }
          encode_dictionary_symbol(this_symbol);
          if (sd[this_symbol].type & 4) {
            add_symbol_to_mtfg_queue(this_symbol);
          }
        }
      }
      prior_end = sd[this_symbol].ends;
    }
    return;
  }

  // write the define code
  if (in_definition == 0) {
    EncodeNewType(LEVEL0);
  }
  else {
    EncodeNewType(LEVEL1);
  }

  define_symbol_instances = sd[define_symbol].count;
  if (define_symbol_instances != 1)
    new_symbol_code_length = sd[define_symbol].code_length;
  else
    new_symbol_code_length = 0x20;

  // send symbol length, instances and ergodicity bit
  if (define_symbol < start_my_symbols) {
    symbol_lengths[define_symbol] = new_symbol_code_length;
    SIDSymbol = 0;
    if (define_symbol_instances == 1)
      Symbol = MAX_INSTANCES_FOR_MTF_QUEUE - 1;
    else if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE)
      Symbol = define_symbol_instances - 2;
    else
      Symbol = MAX_INSTANCES_FOR_MTF_QUEUE + (U32)(max_regular_code_length - new_symbol_code_length);
    EncodeSID(NOT_CAP);
    EncodeINST(NOT_CAP);
    BaseSymbol = define_symbol;
    EncodeBaseSymbol(base_bits);
    U8 j1 = 0xFF;
    do {
      InitNewFirstCharBinBinary(j1, BaseSymbol, new_symbol_code_length);
    } while (j1--);
    j1 = 0xFF;
    do {
      InitNewLastCharBinBinary(BaseSymbol, j1, sd[j1].code_length);
    } while (j1--);
    prior_end = BaseSymbol;

    if (found_first_symbol == 0) {
      found_first_symbol = 1;
      end_symbol = prior_end;
      sym_list_ptrs[end_symbol][max_code_length][0] = end_symbols;
      nsob[end_symbol][max_code_length] = 1;
      nbob[end_symbol][max_code_length] = 1;
      if (max_code_length >= 12) {
        nbob_shift[end_symbol] = max_code_length - 12;
        nbob[end_symbol][max_code_length] = 1;
        sum_nbob[end_symbol] = 1;
      }
      else {
        nbob[end_symbol][max_code_length] = 1 << (12 - max_code_length);
        sum_nbob[end_symbol] = 1 << (12 - max_code_length);
      }
    }
  }
  else {
    num_grammar_rules++;
    this_define_symbol_start_ptr = symbol + sd[define_symbol].define_symbol_start_index;
    define_string_ptr = this_define_symbol_start_ptr;
    define_string_end_ptr = symbol + sd[define_symbol+1].define_symbol_start_index - 1;

    // count the symbols in the definition
    symbols_in_definition = 0;
    while (define_string_ptr != define_string_end_ptr) {
      if ((sd[*define_string_ptr].count != 1) || (*define_string_ptr < start_my_symbols))
        symbols_in_definition++;
      else
        symbols_in_definition += count_symbols(*define_string_ptr);
      define_string_ptr++;
    }
    if (symbols_in_definition < 16) {
      SIDSymbol = symbols_in_definition - 1;;
      EncodeSID(NOT_CAP);
    }
    else {
      SIDSymbol = 15;
      EncodeSID(NOT_CAP);
      S32 extra_symbols = symbols_in_definition - 16;
      S32 temp2 = extra_symbols;
      U8 data_bits = 1;
      while (temp2 >= (1 << data_bits))
        temp2 -= (1 << data_bits++);
      temp2 = (S32)data_bits;
      while (temp2 > 2) {
        temp2 -= 2;
        Symbol = 3;
        EncodeExtraLength();
      }
      extra_symbols += 2 - (1 << data_bits);
      if (temp2 == 2) {
        Symbol = 2;
        EncodeExtraLength();
      }
      else
        data_bits++;
      while (data_bits) {
        data_bits -= 2;
        Symbol = (extra_symbols >> data_bits) & 3;
        EncodeExtraLength();
      }
    }

    if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE)
      Symbol = define_symbol_instances - 2;
    else
      Symbol = MAX_INSTANCES_FOR_MTF_QUEUE + (U32)(max_regular_code_length - new_symbol_code_length);
    EncodeINST(NOT_CAP);

    // write the symbol string
    define_string_ptr = this_define_symbol_start_ptr;
    while (define_string_ptr != define_string_end_ptr) {
      this_symbol = *define_string_ptr++;
      symbol_inst = sd[this_symbol].inst_found++;
      this_symbol_count = sd[this_symbol].count;
      if (symbol_inst == 0)
        embed_define_binary(this_symbol, 1);
      else if (this_symbol_count <= MAX_INSTANCES_FOR_MTF_QUEUE) {
        if (use_mtf) {
          manage_mtf_queue(this_symbol,symbol_inst,this_symbol_count,1);
        }
        else {
          manage_mtf_symbol(this_symbol,symbol_inst,this_symbol_count,1);
        }
      }
      else {
        CodeLength = sd[this_symbol].code_length;
        if (sd[this_symbol].type & 8) {
          if (prior_is_cap == 0) {
            manage_mtfg_queue(this_symbol,1);
          }
          else {
            manage_mtfg_queue_prior_cap(this_symbol,1);
          }
        }
        else {
          EncodeDictType(LEVEL1);
          encode_dictionary_symbol(this_symbol);
          if (sd[this_symbol].type & 4) {
            add_symbol_to_mtfg_queue(this_symbol);
          }
        }
      }
      prior_end = sd[this_symbol].ends;
    }
  }

  if (define_symbol_instances != 1) { // assign symbol code
    if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE) {
      if (use_mtf) {
        mtf_queue_number = define_symbol_instances - 2;
        UpFreqMtfQueueNum(NOT_CAP);
        // Handle initial mtf symbol instance
        sd[define_symbol].type |= 8;
        if (mtf_queue_size[define_symbol_instances] < MTF_QUEUE_SIZE)
          mtf_queue[define_symbol_instances][mtf_queue_size[define_symbol_instances]++] = define_symbol;
        else {
          symbol_to_move = mtf_queue[define_symbol_instances][0];
          sd[symbol_to_move].type &= 0xF7;
          add_dictionary_symbol(symbol_to_move, new_symbol_code_length);
          for (i1=0 ; i1<63 ; i1++)
            mtf_queue[define_symbol_instances][i1] = mtf_queue[define_symbol_instances][i1+1];
          mtf_queue[define_symbol_instances][63] = define_symbol;
        }
      }
      else {
        add_dictionary_symbol(define_symbol, new_symbol_code_length);
      }
    }
    else {
      if (use_mtf && (new_symbol_code_length >= 11)) {
        EncodeERG(0, (sd[define_symbol].type & 4) >> 2);
        if (sd[define_symbol].type & 4) {
          add_symbol_to_mtfg_queue(define_symbol);
        }
      }
      add_dictionary_symbol(define_symbol, new_symbol_code_length);
    }
  }
  num_define_symbols_written++;
  return;
}


void embed_define(U32 define_symbol, U8 in_definition) {
  U32 *define_string_ptr, *this_define_symbol_start_ptr, *define_string_end_ptr;
  U32 define_symbol_instances, symbols_in_definition, symbol_inst, i1, this_symbol, this_symbol_count;
  U8 new_symbol_code_length, char_before_define_is_cap;

  if ((sd[define_symbol].count == 1) && (define_symbol >= start_my_symbols)) {
    // write the symbol string instead of creating a single instance symbol (artifacts of TreeCompress)
    rules_reduced++;
    define_string_ptr = symbol + sd[define_symbol].define_symbol_start_index;
    define_string_end_ptr = symbol + sd[define_symbol+1].define_symbol_start_index - 1;
    while (define_string_ptr != define_string_end_ptr) {
      this_symbol = *define_string_ptr++;
      symbol_inst = sd[this_symbol].inst_found++;
      define_symbol_instances = sd[this_symbol].count;
      if (symbol_inst == 0)
        embed_define(this_symbol, in_definition);
      else if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE) {
        if (use_mtf) {
          manage_mtf_queue(this_symbol,symbol_inst,define_symbol_instances,in_definition);
        }
        else {
          manage_mtf_symbol(this_symbol,symbol_inst,define_symbol_instances,in_definition);
        }
        prior_symbol = this_symbol;
      }
      else {
        if (sd[this_symbol].type & 8) {
          if (prior_is_cap == 0) {
            manage_mtfg_queue(this_symbol,in_definition);
          }
          else {
            manage_mtfg_queue_prior_cap(this_symbol,in_definition);
          }
          prior_is_cap = cap_encoded & sd[this_symbol].type;
        }
        else {
          CodeLength = sd[this_symbol].code_length;
          if (prior_is_cap == 0) {
            if (in_definition == 0) {
              EncodeDictType(LEVEL0);
            }
            else {
              EncodeDictType(LEVEL1);
            }
            prior_is_cap = cap_encoded & sd[this_symbol].type;
          }
          else {
            if (in_definition == 0) {
              EncodeDictType(LEVEL0_CAP);
            }
            else {
              EncodeDictType(LEVEL1_CAP);
            }
            prior_is_cap = sd[this_symbol].type & 1;
          }
          encode_dictionary_symbol(this_symbol);
          if (sd[this_symbol].type & 4) {
            add_symbol_to_mtfg_queue(this_symbol);
          }
        }
        prior_symbol = this_symbol;
      }
      prior_end = sd[this_symbol].ends;
    }
    if ((sd[define_symbol].type & 0x40) == 0)
      sd[define_symbol].type |= sd[symbol[sd[define_symbol+1].define_symbol_start_index - 2]].type & 0xC0;
    return;
  }

  // write the define code
  if (prior_is_cap == 0) {
    if (in_definition == 0) {
      EncodeNewType(LEVEL0);
    }
    else {
      EncodeNewType(LEVEL1);
    }
  }
  else {
    if (in_definition == 0) {
      EncodeNewType(LEVEL0_CAP);
    }
    else {
      EncodeNewType(LEVEL1_CAP);
    }
  }

  define_symbol_instances = sd[define_symbol].count;
  if (define_symbol_instances != 1)
    new_symbol_code_length = sd[define_symbol].code_length;
  else
    new_symbol_code_length = 0x20;

  // send symbol length, instances and ergodicity bit
  if (define_symbol < start_my_symbols) {
    SIDSymbol = 0;
    if (define_symbol_instances == 1)
      Symbol = MAX_INSTANCES_FOR_MTF_QUEUE - 1;
    else if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE)
      Symbol = define_symbol_instances - 2;
    else
      Symbol = MAX_INSTANCES_FOR_MTF_QUEUE + (U32)(max_regular_code_length - new_symbol_code_length);
    if (prior_is_cap == 0) {
      EncodeSID(NOT_CAP);
      EncodeINST(NOT_CAP);
    }
    else {
      EncodeSID(CAP);
      EncodeINST(CAP);
    }
    BaseSymbol = define_symbol;
    EncodeBaseSymbol(base_bits);
    if (cap_encoded) {
      if (UTF8_compliant) {
        if (BaseSymbol < 0x80) {
          symbol_lengths[define_symbol] = new_symbol_code_length;
          InitNewBaseSymbolCap(0x80);
          prior_end = BaseSymbol;
          if (prior_end == 'B')
            prior_end = 'C';
        }
        else {
          prior_end = 0x80;
          if (RangeScaleFirstChar[0][0x80] == 0) {
            symbol_lengths[0x80] = new_symbol_code_length;
            U8 j1 = 0x7F;
            do {
              InitNewFirstCharBin(j1, 0x80, new_symbol_code_length);
            } while (--j1 != 'Z');
            j1 = 'A' - 1;
            do {
              InitNewFirstCharBin(j1, 0x80, new_symbol_code_length);
            } while (j1--);
            j1 = 0x80;
            do {
              InitSymbolFirstChar(0x80, j1);
              if (RangeScaleFirstChar[0][j1]) {
                InitNewLastCharBin(0x80, j1, symbol_lengths[j1]);
              }
              else if ((j1 == 'C') && cap_symbol_defined) {
                InitNewLastCharBin(0x80, 'C', symbol_lengths[j1]);
              }
              else if ((j1 == 'B') && cap_lock_symbol_defined) {
                InitNewLastCharBin(0x80, 'B', symbol_lengths[j1]);
              }
            } while (j1--);
            InitFreqFirstChar(0x80, 0x80);
            IncrementRangeScaleFirstChar(0x80);
          }
        }
      }
      else {
        symbol_lengths[define_symbol] = new_symbol_code_length;
        InitNewBaseSymbolCap(0xFF);
        prior_end = BaseSymbol;
      }
    }
    else {
      if (UTF8_compliant) {
        if (BaseSymbol < 0x80) {
          symbol_lengths[define_symbol] = new_symbol_code_length;
          U8 j1 = 0x80;
          do {
            InitNewFirstCharBin(j1, BaseSymbol, new_symbol_code_length);
          } while (j1--);
          j1 = 0x80;
          do {
            InitSymbolFirstChar(BaseSymbol, j1);
            if (RangeScaleFirstChar[0][j1] || (j1 == BaseSymbol)) {
              InitNewLastCharBin(BaseSymbol, j1, symbol_lengths[j1]);
            }
          } while (j1--);
        }
        else if (RangeScaleFirstChar[0][0x80] == 0) {
          symbol_lengths[0x80] = new_symbol_code_length;
          U8 j1 = 0x7F;
          do {
            InitNewFirstCharBin(j1, 0x80, new_symbol_code_length);
          } while (j1--);
          j1 = 0x80;
          do {
            InitSymbolFirstChar(0x80, j1);
            if (RangeScaleFirstChar[0][j1]) {
              InitNewLastCharBin(0x80, j1, symbol_lengths[j1]);
            }
          } while (j1--);
          InitFreqFirstChar(0x80, 0x80);
          IncrementRangeScaleFirstChar(0x80);
        }
        prior_end = BaseSymbol;
        if (prior_end > 0x80)
          prior_end = 0x80;
      }
      else {
        symbol_lengths[define_symbol] = new_symbol_code_length;
        U8 j1 = 0xFF;
        do {
          InitNewFirstCharBin(j1, BaseSymbol, new_symbol_code_length);
        } while (j1--);
        j1 = 0xFF;
        do {
          InitSymbolFirstChar(BaseSymbol, j1);
          if (RangeScaleFirstChar[0][j1] || (j1 == BaseSymbol)) {
            InitNewLastCharBin(BaseSymbol, j1, symbol_lengths[j1]);
          }
        } while (j1--);
        prior_end = BaseSymbol;
      }
    }
    prior_symbol = BaseSymbol;

    char_before_define_is_cap = prior_is_cap;
    prior_is_cap = cap_encoded & sd[define_symbol].type;
    if (found_first_symbol == 0) {
      found_first_symbol = 1;
      end_symbol = prior_end;
      sym_list_ptrs[end_symbol][max_code_length][0] = end_symbols;
      nsob[end_symbol][max_code_length] = 1;
      nbob[end_symbol][max_code_length] = 1;
      if (max_code_length >= 12) {
        nbob_shift[end_symbol] = max_code_length - 12;
        nbob[end_symbol][max_code_length] = 1;
        sum_nbob[end_symbol] = 1;
      }
      else {
        nbob[end_symbol][max_code_length] = 1 << (12 - max_code_length);
        sum_nbob[end_symbol] = 1 << (12 - max_code_length);
      }
    }
  }
  else {
    num_grammar_rules++;
    this_define_symbol_start_ptr = symbol + sd[define_symbol].define_symbol_start_index;
    define_string_ptr = this_define_symbol_start_ptr;
    define_string_end_ptr = symbol + sd[define_symbol+1].define_symbol_start_index - 1;

    // count the symbols in the definition
    symbols_in_definition = 0;
    while (define_string_ptr != define_string_end_ptr) {
      if ((sd[*define_string_ptr].count != 1) || (*define_string_ptr < start_my_symbols))
        symbols_in_definition++;
      else
        symbols_in_definition += count_symbols(*define_string_ptr);
      define_string_ptr++;
    }
    if (symbols_in_definition < 16) {
      SIDSymbol = symbols_in_definition - 1;;
      if (prior_is_cap == 0) {
        EncodeSID(NOT_CAP);
      }
      else {
        EncodeSID(CAP);
      }
    }
    else {
      SIDSymbol = 15;
      if (prior_is_cap == 0) {
        EncodeSID(NOT_CAP);
      }
      else {
        EncodeSID(CAP);
      }
      S32 extra_symbols = symbols_in_definition - 16;
      S32 temp2 = extra_symbols;
      U8 data_bits = 1;
      while (temp2 >= (1 << data_bits))
        temp2 -= (1 << data_bits++);
      temp2 = (S32)data_bits;
      while (temp2 > 2) {
        temp2 -= 2;
        Symbol = 3;
        EncodeExtraLength();
      }
      extra_symbols += 2 - (1 << data_bits);
      if (temp2 == 2) {
        Symbol = 2;
        EncodeExtraLength();
      }
      else
        data_bits++;
      while (data_bits) {
        data_bits -= 2;
        Symbol = (extra_symbols >> data_bits) & 3;
        EncodeExtraLength();
      }
    }

    if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE)
      Symbol = define_symbol_instances - 2;
    else
      Symbol = MAX_INSTANCES_FOR_MTF_QUEUE + (U32)(max_regular_code_length - new_symbol_code_length);
    if (prior_is_cap == 0) {
      EncodeINST(NOT_CAP);
    }
    else {
      EncodeINST(CAP);
    }

    char_before_define_is_cap = prior_is_cap;

    // write the symbol string
    define_string_ptr = this_define_symbol_start_ptr;
    while (define_string_ptr != define_string_end_ptr) {
      this_symbol = *define_string_ptr++;
      symbol_inst = sd[this_symbol].inst_found++;
      this_symbol_count = sd[this_symbol].count;
      if (symbol_inst == 0)
        embed_define(this_symbol, 1);
      else if (this_symbol_count <= MAX_INSTANCES_FOR_MTF_QUEUE) {
        if (use_mtf) {
          manage_mtf_queue(this_symbol,symbol_inst,this_symbol_count,1);
        }
        else {
          manage_mtf_symbol(this_symbol,symbol_inst,this_symbol_count,1);
        }
        prior_symbol = this_symbol;
      }
      else {
        CodeLength = sd[this_symbol].code_length;
        if (sd[this_symbol].type & 8) {
          if (prior_is_cap == 0) {
            manage_mtfg_queue(this_symbol,1);
          }
          else {
            manage_mtfg_queue_prior_cap(this_symbol,1);
          }
          prior_is_cap = cap_encoded & sd[this_symbol].type;
        }
        else {
          if (prior_is_cap == 0) {
            EncodeDictType(LEVEL1);
            prior_is_cap = cap_encoded & sd[this_symbol].type;
          }
          else {
            EncodeDictType(LEVEL1_CAP);
            prior_is_cap = sd[this_symbol].type & 1;
          }
          encode_dictionary_symbol(this_symbol);
          if (sd[this_symbol].type & 4) {
            add_symbol_to_mtfg_queue(this_symbol);
          }
        }
        prior_symbol = this_symbol;
      }
      prior_end = sd[this_symbol].ends;
    }
    prior_symbol = define_symbol;
  }

  if (define_symbol_instances != 1) { // assign symbol code
    U8 tag_type = 0;
    if (cap_encoded) {
      if (sd[define_symbol].type & 0x40) {
        if (sd[define_symbol].type & 0x80) {
          tag_type = 2;
          EncodeWordTag(1);
        }
        else {
          tag_type = 1;
          EncodeWordTag(0);
        }
      }
      else if (define_symbol >= start_my_symbols)
        sd[define_symbol].type |= sd[symbol[sd[define_symbol+1].define_symbol_start_index - 2]].type & 0xC0;
    }
    if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE) {
      if (use_mtf) {
        mtf_queue_number = define_symbol_instances - 2;
        if (char_before_define_is_cap == 0) {
          UpFreqMtfQueueNum(NOT_CAP);
        }
        else {
          UpFreqMtfQueueNum(CAP);
        }
        // Handle initial mtf symbol instance
        sd[define_symbol].type |= 8;
        if (mtf_queue_size[define_symbol_instances] < MTF_QUEUE_SIZE)
          mtf_queue[define_symbol_instances][mtf_queue_size[define_symbol_instances]++] = define_symbol;
        else {
          symbol_to_move = mtf_queue[define_symbol_instances][0];
          sd[symbol_to_move].type &= 0xF7;
          add_dictionary_symbol(symbol_to_move, new_symbol_code_length);
          for (i1=0 ; i1<63 ; i1++)
            mtf_queue[define_symbol_instances][i1] = mtf_queue[define_symbol_instances][i1+1];
          mtf_queue[define_symbol_instances][63] = define_symbol;
        }
      }
      else {
        add_dictionary_symbol(define_symbol, new_symbol_code_length);
      }
    }
    else {
      if (use_mtf && (new_symbol_code_length >= 11)) {
        EncodeERG(tag_type, (sd[define_symbol].type & 4) >> 2);
        if (sd[define_symbol].type & 4) {
          add_symbol_to_mtfg_queue(define_symbol);
        }
      }
      add_dictionary_symbol(define_symbol, new_symbol_code_length);
    }
  }
  num_define_symbols_written++;
  return;
}


int main(int argc, char* argv[]) {
  FILE *fd_in, *fd_out;
  U8 this_char, arg_num, verbose;
  U32 i1, i2, in_size, num_symbols, num_symbols_defined, num_definitions_to_code, num_chars_to_read, grammar_size;
  U32 UTF8_value, max_UTF8_value, this_symbol, this_symbol_count, symbol_inst, prior_inst, next_symbol;
  U32 min_ranked_symbols, ranked_symbols_save, num_ranked_symbols, num_regular_definitions;
  U32 mtf_queue_hits, mtfg_symbols_reduced, mtf_overflow_symbols_to_code;
  U32 *end_symbol_ptr;
  U32 *ranked_symbols_ptr, *end_ranked_symbols_ptr, *min_ranked_symbols_ptr, *max_ranked_symbols_ptr;
  U32 *min_one_instance_ranked_symbols_ptr, *next_sorted_symbol_ptr;
  S32 remaining_symbols_to_code, remaining_code_space;
  double d_remaining_symbols_to_code, symbol_inst_factor;
  time_t start_time;


  start_time = clock();

  for (i1 = 2 ; i1 <= MAX_INSTANCES_FOR_MTF_QUEUE ; i1++) {
    mtf_queue_started[i1] = 0;
    mtf_queue_done[i1] = 0;
    mtf_queue_peak[i1] = 0;
    mtf_queue_size[i1] = 0;
    for (i2 = 0 ; i2 < MTF_QUEUE_SIZE ; i2++)
      mtf_queue_hit_count[i1][i2] = 0;
  }
  mtfg_queue_8_offset = 0;
  mtfg_queue_16_offset = 0;
  mtfg_queue_32_offset = 0;
  mtfg_queue_64_offset = 0;
  mtfg_queue_128_offset = 0;
  mtfg_queue_192_offset = 0;

  arg_num = 1;
  verbose = 0;
  use_mtf = 2;
  while (*argv[arg_num] ==  '-') {
    if (*argv[arg_num] ==  '-') {
      if (*(argv[arg_num]+1) == 'v') {
        verbose = 1;
        if (*(argv[arg_num]+2) == '1')
          verbose = 2;
      }
      else if (*(argv[arg_num]+1) == 'm') {
        use_mtf = *(argv[arg_num]+2) - '0';
        if (use_mtf > 1) {
          fprintf(stderr,"ERROR - Invalid '-' format.  Only -v, -m0 or -m1 allowed\n");
          exit(0);
        }
      }
      else {
        fprintf(stderr,"ERROR - Invalid '-' format.  Only -v, -m0 or -m1 allowed\n");
        exit(0);
      }
      arg_num++;
    }
  }
  if((fd_in=fopen(argv[arg_num],"rb")) == NULL) {
    fprintf(stderr,"fopen error - '%s'\n",argv[arg_num]);
    exit(0);
  }
  arg_num++;

  // read the file into local memory
  fseek(fd_in, 0, SEEK_END);
  in_size = ftell(fd_in);
  if (in_size == 0) {
    fclose(fd_in);
    if((fd_out = fopen(argv[arg_num],"wb")) == NULL) {
      printf("fopen error - file '%s' not found\n",argv[arg_num]);
      exit(0);
    }
    fclose(fd_out);
    return(0);
  }
  rewind(fd_in);

  in_char_ptr = in_data;
  end_char_ptr = in_data + in_size;
  fread(in_data,1,READ_SIZE+3,fd_in);
  num_chars_to_read = in_size - READ_SIZE - 3;
  num_symbols = 0;

  cap_encoded = *in_char_ptr & 1; 
  delta_format = *in_char_ptr++ >> 1;
  stride = delta_format & 7;
  UTF8_compliant = 1;
  max_UTF8_value = 0x7F;

  // parse the file to determine UTF8_compliant
  while (in_char_ptr != end_char_ptr) {
    if (in_char_ptr - in_data  >= READ_SIZE) {
      *in_data = *(in_data + READ_SIZE);
      *(in_data + 1) = *(in_data + READ_SIZE + 1);
      *(in_data + 2) = *(in_data + READ_SIZE + 2);
      in_char_ptr -= READ_SIZE;
      end_char_ptr -= READ_SIZE;
      if (num_chars_to_read >= READ_SIZE) {
        fread(in_data+3,1,READ_SIZE,fd_in);
        num_chars_to_read -= READ_SIZE;
      }
      else {
        fread(in_data+3,1,num_chars_to_read,fd_in);
        num_chars_to_read = 0;
      }
    }

    if (*in_char_ptr >= INSERT_SYMBOL_CHAR) {
      if (*(in_char_ptr+1) != DEFINE_SYMBOL_CHAR)
        in_char_ptr += 4;
      else {
        UTF8_compliant = 0;
        break;
      }
    }
    else if (*in_char_ptr >= 0x80) {
      if (*in_char_ptr < 0xC0) {
        UTF8_compliant = 0;
        break;
      }
      else if (*in_char_ptr < 0xE0) {
        if ((*(in_char_ptr+1) < 0x80) || (*(in_char_ptr+1) >= 0xC0)) {
          UTF8_compliant = 0;
          break;
        }
        else {
          UTF8_value = 0x40 * (*in_char_ptr & 0x1F) + (*(in_char_ptr+1) & 0x3F);
          if (UTF8_value > max_UTF8_value)
            max_UTF8_value = UTF8_value;
          in_char_ptr += 2;
        }
      }
      else if (*in_char_ptr < 0xF0) {
        if ((*(in_char_ptr+1) < 0x80) || (*(in_char_ptr+1) >= 0xC0)
            || (*(in_char_ptr+2) < 0x80) || (*(in_char_ptr+2) >= 0xC0)) {
          UTF8_compliant = 0;
          break;
        }
        else {
          UTF8_value = 0x1000 * (*in_char_ptr & 0xF) + 0x40 * (*(in_char_ptr+1) & 0x3F) + (*(in_char_ptr+2) & 0x3F);
          if (UTF8_value > max_UTF8_value)
            max_UTF8_value = UTF8_value;
          in_char_ptr += 3;
        }
      }
      else if (*in_char_ptr < 0xF8) {
        if ((*(in_char_ptr+1) < 0x80) || (*(in_char_ptr+1) >= 0xC0) || (*(in_char_ptr+2) < 0x80)
            || (*(in_char_ptr+2) >= 0xC0) || (*(in_char_ptr+3) < 0x80) || (*(in_char_ptr+3) >= 0xC0)) {
          UTF8_compliant = 0;
          break;
        }
        else {
          UTF8_value = 0x40000 * (*in_char_ptr & 0x7) + 0x1000 * (*(in_char_ptr+1) & 0x3F)
              + 0x40 * (*(in_char_ptr+2) & 0x3F) + (*(in_char_ptr+3) & 0x3F);
          if (UTF8_value > max_UTF8_value)
            max_UTF8_value = UTF8_value;
          in_char_ptr += 4;
        }
      }
      else {
        UTF8_compliant = 0;
        break;
      }
    }
    else
      in_char_ptr++;
    num_symbols++;
  }

  rewind(fd_in);
  fread(in_data,1,READ_SIZE+3,fd_in);
  num_chars_to_read = in_size - READ_SIZE - 3;
  in_char_ptr = in_data + 1;
  end_char_ptr = in_data + in_size;
  num_symbols_defined = 0;
  rules_reduced = 0;

  symbol = 0;
  if (in_size <= MAX_FILE_SIZE) {
    if (UTF8_compliant)
      symbol = (U32 *)malloc(sizeof(U32) * (num_symbols + 1));
    else
      symbol = (U32 *)malloc(sizeof(U32) * (in_size + 1));
  }
  if (symbol == 0) {
    fprintf(stderr,"Symbol memory allocation failed\n");
    exit(0);
  }
  symbol_ptr = symbol;

  start_my_symbols = 0x00080000;

  if (UTF8_compliant) {
    base_bits = 0;
    while (max_UTF8_value >> base_bits)
      base_bits++;
    start_my_symbols = 1 << base_bits;
    while (in_char_ptr < end_char_ptr) {
      if (in_char_ptr - in_data >= READ_SIZE) {
        if (symbol_ptr - symbol >= MAX_FILE_SIZE - READ_SIZE) {
          fprintf(stderr,"ERROR - symbol limit of %u symbols exceeded\n",MAX_FILE_SIZE);
          exit(0);
        }
        *in_data = *(in_data + READ_SIZE);
        *(in_data + 1) = *(in_data + READ_SIZE + 1);
        *(in_data + 2) = *(in_data + READ_SIZE + 2);
        in_char_ptr -= READ_SIZE;
        end_char_ptr -= READ_SIZE;
        if (num_chars_to_read >= READ_SIZE) {
          fread(in_data+3,1,READ_SIZE,fd_in);
          num_chars_to_read -= READ_SIZE;
        }
        else {
          fread(in_data+3,1,num_chars_to_read,fd_in);
          num_chars_to_read = 0;
        }
      }

      this_char = *in_char_ptr++;
      if (this_char == INSERT_SYMBOL_CHAR) {
        this_symbol = start_my_symbols;
        this_symbol += 0x10000 * (U32)*in_char_ptr++;
        this_symbol += 0x100 * (U32)*in_char_ptr++;
        this_symbol += (U32)*in_char_ptr++;
        *symbol_ptr++ = this_symbol;
      }
      else if (this_char == DEFINE_SYMBOL_CHAR) {
        if (first_define_ptr == 0)
          first_define_ptr = symbol_ptr;
        in_char_ptr += 3;
        *symbol_ptr++ = ((U32)DEFINE_SYMBOL_CHAR << 24) + num_symbols_defined++;
      }
      else if (this_char < START_UTF8_2BYTE_SYMBOLS)
        *symbol_ptr++ = (U32)this_char;
      else {
        if (this_char >= 0xF8) { // not a UTF-8 character
          fprintf(stderr,"ERROR - non UTF-8 character %x\n",(unsigned char)this_char);
          exit(0);
        }
        else if (this_char >= 0xF0) { // 4 byte UTF-8 character
          UTF8_value = 0x40000 * (this_char & 7);
          UTF8_value += 0x1000 * (*in_char_ptr++ & 0x3F);
          UTF8_value += 0x40 * (*in_char_ptr++ & 0x3F);
        }
        else if (this_char >= 0xE0) { // 3 byte UTF-8 character
          UTF8_value = 0x1000 * (this_char & 0xF);
          UTF8_value += 0x40 * (*in_char_ptr++ & 0x3F);
        }
        else // 2 byte UTF-8 character
          UTF8_value = 0x40 * (this_char & 0x1F);
        UTF8_value += *in_char_ptr++ & 0x3F;
        *symbol_ptr++ = UTF8_value;
      }
    }
  }
  else {
    base_bits = 8;
    start_my_symbols = 1 << base_bits;
    while (in_char_ptr < end_char_ptr) {
      if (symbol_ptr - symbol == MAX_FILE_SIZE) {
        fprintf(stderr,"ERROR - symbol limit of %u symbols exceeded\n",MAX_FILE_SIZE);
        exit(0);
      }
      if (in_char_ptr - in_data  >= READ_SIZE) {
        *in_data = *(in_data + READ_SIZE);
        *(in_data + 1) = *(in_data + READ_SIZE + 1);
        *(in_data + 2) = *(in_data + READ_SIZE + 2);
        in_char_ptr -= READ_SIZE;
        end_char_ptr -= READ_SIZE;
        if (num_chars_to_read >= READ_SIZE) {
          fread(in_data+3,1,READ_SIZE,fd_in);
          num_chars_to_read -= READ_SIZE;
        }
        else {
          fread(in_data+3,1,num_chars_to_read,fd_in);
          num_chars_to_read = 0;
        }
      }
      this_char = *in_char_ptr++;
      if (this_char < INSERT_SYMBOL_CHAR)
        *symbol_ptr++ = (U32)this_char;
      else if (*in_char_ptr == DEFINE_SYMBOL_CHAR) {
        *symbol_ptr++ = (U32)this_char;
        in_char_ptr++;
      }
      else if (this_char == INSERT_SYMBOL_CHAR) {
        this_symbol = start_my_symbols;
        this_symbol += 0x10000 * (U32)*in_char_ptr++;
        this_symbol += 0x100 * (U32)*in_char_ptr++;
        this_symbol += (U32)*in_char_ptr++;
        *symbol_ptr++ = this_symbol;
      }
      else {
        if (first_define_ptr == 0)
          first_define_ptr = symbol_ptr;
        in_char_ptr += 3;
        *symbol_ptr++ = ((U32)DEFINE_SYMBOL_CHAR << 24) + num_symbols_defined++;
      }
    }
  }
  fclose(fd_in);
  fprintf(stderr,"cap encoded %u, UTF8 compliant %u\n",(unsigned int)cap_encoded,(unsigned int)UTF8_compliant);

  if (first_define_ptr == 0)
    first_define_ptr = symbol_ptr;
  grammar_size = symbol_ptr - symbol;

  *symbol_ptr = UNIQUE_CHAR;
  end_symbol_ptr = symbol_ptr;
  num_symbols = end_symbol_ptr - symbol;
  end_symbols = start_my_symbols + num_symbols_defined;
  fprintf(stderr,"Read %u symbols including %u definition symbols\n",(unsigned int)num_symbols,(unsigned int)num_symbols_defined);

  if (0 == (sd = (struct symbol_data *)malloc(sizeof(struct symbol_data) * (end_symbols + 1)))) {
    fprintf(stderr,"Symbol data memory allocation failed\n");
    exit(0);
  }

  if (0 == (ranked_symbols = (U32 *)malloc(sizeof(U32) * end_symbols))) {
    fprintf(stderr,"Ranked symbol array memory allocation failed\n");
    exit(0);
  }

  // count the number of instances of each symbol
  for (i1 = 0 ; i1 < end_symbols ; i1++) {
    sd[i1].count = 0;
    sd[i1].inst_found = 0;
  }
  symbol_ptr = symbol;
  num_symbols_defined = 0;
  while (1) {
    if (*symbol_ptr < (U32)DEFINE_SYMBOL_CHAR << 24)
      sd[*symbol_ptr++].count++;
    else if (*symbol_ptr++ != UNIQUE_CHAR) {
      sd[start_my_symbols + num_symbols_defined++].define_symbol_start_index = symbol_ptr - symbol;
    }
    else
      break;
  }
  sd[start_my_symbols + num_symbols_defined].define_symbol_start_index = symbol_ptr - symbol;

  if (cap_encoded) {
    i1 = 0;
    do {
      sd[i1].type = 0;
    } while (++i1 != 0x61);
    do {
      sd[i1].type = 2;
    } while (++i1 != 0x7B);
    do {
      sd[i1].type = 0;
    } while (++i1 != start_my_symbols);
    sd['B'].type = 1;
    sd['C'].type = 1;
    while (i1 < end_symbols) {
      next_symbol = symbol[sd[i1].define_symbol_start_index];
      while (next_symbol > i1)
        next_symbol = symbol[sd[next_symbol].define_symbol_start_index];
      sd[i1].type = sd[next_symbol].type & 2;
      next_symbol = symbol[sd[i1+1].define_symbol_start_index-2];
      while (next_symbol > i1)
        next_symbol = symbol[sd[next_symbol+1].define_symbol_start_index-2];
      sd[i1].type |= sd[next_symbol].type & 1;
      i1++;
    }
  }
  else {
    i1 = 0;
    while (i1 < end_symbols)
      sd[i1++].type = 0;
  }

  ranked_symbols_ptr = ranked_symbols;
  for (i1=0 ; i1<end_symbols ; i1++)
    if (sd[i1].count)
      *ranked_symbols_ptr++ = i1;
  end_ranked_symbols_ptr = ranked_symbols_ptr;
  min_ranked_symbols_ptr = ranked_symbols_ptr;

  // move single instance symbols to the end of the sorted symbols array
  ranked_symbols_ptr = ranked_symbols;
  while (ranked_symbols_ptr < min_ranked_symbols_ptr) {
    if (sd[*ranked_symbols_ptr].count == 1) { // move this symbol to the top of the moved to end 1 instance symbols
      ranked_symbols_save = *ranked_symbols_ptr;
      *ranked_symbols_ptr = *--min_ranked_symbols_ptr;
      *min_ranked_symbols_ptr = ranked_symbols_save;
    }
    else
      ranked_symbols_ptr++;
  }
  min_one_instance_ranked_symbols_ptr = min_ranked_symbols_ptr;

  // sort symbols with 800 or fewer instances by putting them at the end of the sorted symbols array
  for (i1=2 ; i1<801 ; i1++) {
    ranked_symbols_ptr = ranked_symbols;
    while (ranked_symbols_ptr < min_ranked_symbols_ptr) {
      if (sd[*ranked_symbols_ptr].count == i1) {
        ranked_symbols_save = *ranked_symbols_ptr;
        *ranked_symbols_ptr = *--min_ranked_symbols_ptr;
        *min_ranked_symbols_ptr = ranked_symbols_save;
      }
      else
        ranked_symbols_ptr++;
    }
  }

  // sort the remaining symbols by moving the most frequent symbols to the top of the sorted symbols array
  min_ranked_symbols = min_ranked_symbols_ptr - ranked_symbols;
  for (i1=0 ; i1<min_ranked_symbols ; i1++) {
    U32 max_symbol_count = 0;
    ranked_symbols_ptr = &ranked_symbols[i1];
    while (ranked_symbols_ptr < min_ranked_symbols_ptr) {
      if (sd[*ranked_symbols_ptr].count > max_symbol_count) {
        max_symbol_count = sd[*ranked_symbols_ptr].count;
        max_ranked_symbols_ptr = ranked_symbols_ptr;
      }
      ranked_symbols_ptr++;
    }
    if (max_symbol_count > 0) {
      ranked_symbols_save = ranked_symbols[i1];
      ranked_symbols[i1] = *max_ranked_symbols_ptr;
      *max_ranked_symbols_ptr = ranked_symbols_save;
    }
  }
  num_ranked_symbols = end_ranked_symbols_ptr - ranked_symbols;
  num_symbols_to_code = num_symbols - (end_ranked_symbols_ptr - ranked_symbols);
  num_definitions_to_code = min_one_instance_ranked_symbols_ptr - ranked_symbols;
  num_define_symbols_written = 0;

  remaining_symbols_to_code = num_symbols_to_code - num_symbols_defined;
  remaining_code_space = (1 << 30);
  remaining_code_space -= 1 << (30 - MAX_BITS_IN_CODE); // reserve space for EOF
  remaining_code_space -= 0x02000000; // reserve code space for define symbols so they don't get too long

  for (i1 = 2 ; i1 < 5 ; i1++)
    mtf_queue_overflow_code_length[i1] = 25;
  for (i1 = 5 ; i1 < 10 ; i1++)
    mtf_queue_overflow_code_length[i1] = 24;
  for (i1 = 10 ; i1 <= MAX_INSTANCES_FOR_MTF_QUEUE ; i1++)
    mtf_queue_overflow_code_length[i1] = 23;

  remaining_code_space += (remaining_code_space >> 5) - 0x20;
  remaining_symbols_to_code += remaining_symbols_to_code >> 5;
  max_regular_code_length = 1;
  num_regular_definitions = 0;

  prior_inst = 0;
  i1 = 0;
  while (i1 < num_definitions_to_code) {
    symbol_inst = sd[ranked_symbols[i1]].count - 1;
    if (symbol_inst != prior_inst) {
      prior_inst = symbol_inst;
      symbol_inst_factor = 1.4 * (double)0x40000000 / (double)symbol_inst;
      if (symbol_inst <= MAX_INSTANCES_FOR_MTF_QUEUE)
        break;
    }
    d_remaining_symbols_to_code = (double)remaining_symbols_to_code;
    symbol_code_length = (U8)(log2(d_remaining_symbols_to_code * symbol_inst_factor / (double)remaining_code_space));
    if (symbol_code_length < 2) // limit so files with less than 2 bit symbols (ideally) work
      symbol_code_length = 2;
    num_regular_definitions++;
    if (symbol_code_length > 24)
      symbol_code_length = 24;
    if (symbol_code_length > max_regular_code_length)
      max_regular_code_length = symbol_code_length;
    sd[ranked_symbols[i1]].code_length = symbol_code_length;
    remaining_code_space -= (1 << (30 - symbol_code_length));
    remaining_symbols_to_code -= symbol_inst;
    i1++;
  }

  i1 = num_definitions_to_code;
  while (i1 < num_ranked_symbols)
    sd[ranked_symbols[i1++]].code_length = 0x20;

  mtfg_queue_8_offset = 0;
  mtfg_queue_16_offset = 0;
  mtfg_queue_32_offset = 0;
  mtfg_queue_64_offset = 0;
  mtfg_queue_128_offset = 0;
  mtfg_queue_192_offset = 0;
  for (i1 = 0 ; i1 < 8 ; i1++)
    mtfg_queue_0[i1] = end_symbols;
  for (i1 = 0 ; i1 < 8 ; i1++)
    mtfg_queue_8[i1] = end_symbols;
  for (i1 = 0 ; i1 < 16 ; i1++)
    mtfg_queue_16[i1] = end_symbols;
  for (i1 = 0 ; i1 < 32 ; i1++)
    mtfg_queue_32[i1] = end_symbols;
  for (i1 = 0 ; i1 < 64 ; i1++)
    mtfg_queue_64[i1] = end_symbols;
  for (i1 = 0 ; i1 < 64 ; i1++)
    mtfg_queue_128[i1] = end_symbols;
  for (i1 = 0 ; i1 < 64 ; i1++)
    mtfg_queue_192[i1] = end_symbols;

  symbol_ptr = symbol;

  for (i1 = start_my_symbols ; i1 < end_symbols ; i1++) {
    sd[i1].starts = 0;
    sd[i1].ends = 0;
  }

  if (UTF8_compliant) {
    i1 = 0;
    while (i1 < 0x80) {
      sd[i1].starts = (U8)i1;
      sd[i1].ends = (U8)i1;
      i1++;
    }
    while (i1 <= max_UTF8_value) {
      sd[i1].starts = 0x80;
      sd[i1].ends = 0x80;
      i1++;
    }
    if (cap_encoded)
      sd['B'].ends = 'C';
    i1 = start_my_symbols;
    while (i1 < end_symbols) {
      if (sd[i1].starts == 0)
        sd[i1].starts = find_first_UTF8(i1);
      if (sd[i1].ends == 0)
        sd[i1].ends = find_last_UTF8(i1);
      i1++;
    }
  }
  else {
    i1 = 0;
    while (i1 < 0x100) {
      sd[i1].starts = (U8)i1;
      sd[i1].ends = (U8)i1;
      i1++;
    }
    if (cap_encoded)
      sd['B'].ends = 'C';
    i1 = start_my_symbols;
    while (i1 < end_symbols) {
      if (sd[i1].starts == 0)
        sd[i1].starts = find_first(i1);
      if (sd[i1].ends == 0)
        sd[i1].ends = find_last(i1);
      i1++;
    }
  }

  for (i1 = 0 ; i1 < end_symbols; i1++)
    sd[i1].space_score = 0;

  this_symbol = (U32)-1;
  while (symbol_ptr < first_define_ptr) {
    if (((symbol_ptr - symbol) & 0x3FFFFF) == 0)
      fprintf(stderr,"Parsed %u of %u level 0 symbols\r",
          (unsigned int)(symbol_ptr - symbol),(unsigned int)(first_define_ptr - symbol));
    this_symbol = *symbol_ptr++;
    if (prior_symbol >= 0) {
      if (sd[prior_symbol].type & 0x20) {
        if (sd[this_symbol].starts == 0x20)
          sd[prior_symbol].space_score += 2;
        else
          sd[prior_symbol].space_score -= 9;
      }
    }
    this_symbol_count = sd[this_symbol].count;
    symbol_inst = sd[this_symbol].inst_found++;
    if (symbol_inst == 0)
      count_embedded_definition_symbols(this_symbol);
    else if (this_symbol_count <= MAX_INSTANCES_FOR_MTF_QUEUE) {
      update_mtf_queue(this_symbol,symbol_inst,this_symbol_count);
      prior_symbol = this_symbol;
    }
    else {
      CodeLength = sd[this_symbol].code_length;
      if (CodeLength >= 11) {
        if (sd[this_symbol].type & 8) {
          manage_mtfg_queue1(this_symbol);
          sd[this_symbol].mtfg_hits++;
        }
        else {
          add_symbol_to_mtfg_queue(this_symbol);
        }
      }
      prior_symbol = this_symbol;
    }
  }
  fprintf(stderr,"Parsed %u level 0 symbols              \r",(unsigned int)(first_define_ptr - symbol));

  mtfg_symbols_reduced = 0;
  if (use_mtf == 2) {
    use_mtf = 0;
    if ((double)(4 * mtf_queue_started[2]) > (22.8 - log((double)num_symbols)) * (double)mtf_queue_peak[2])
      use_mtf = 1;
  }
  if (use_mtf) {
    for (i1 = 0 ; i1 < end_symbols ; i1++) {
      if ((sd[i1].count > MAX_INSTANCES_FOR_MTF_QUEUE) && (sd[i1].code_length >= 11)
          && (sd[i1].hit_score > ((sd[i1].count * 3) >> 2))) {
        sd[i1].type |= 4;
        if (sd[i1].count - sd[i1].mtfg_hits <= MAX_INSTANCES_FOR_MTF_QUEUE) {
          mtfg_symbols_reduced += sd[i1].count - MAX_INSTANCES_FOR_MTF_QUEUE - 1;
          sd[i1].count = MAX_INSTANCES_FOR_MTF_QUEUE + 1;
        }
        else {
          mtfg_symbols_reduced += sd[i1].mtfg_hits;
          sd[i1].count -= sd[i1].mtfg_hits;
        }
      }
    }
  }

  // sort symbols with 800 or fewer instances by putting them at the end of the sorted symbols array
  next_sorted_symbol_ptr = ranked_symbols + num_regular_definitions - 1;
  for (i1 = MAX_INSTANCES_FOR_MTF_QUEUE + 1 ; i1 < 801 ; i1++) {
    while ((next_sorted_symbol_ptr > ranked_symbols) && (sd[*next_sorted_symbol_ptr].count == i1))
      next_sorted_symbol_ptr--;
    ranked_symbols_ptr = next_sorted_symbol_ptr - 1;
    while (ranked_symbols_ptr >= ranked_symbols) {
      if (sd[*ranked_symbols_ptr].count == i1) {
        ranked_symbols_save = *ranked_symbols_ptr;
        *ranked_symbols_ptr-- = *next_sorted_symbol_ptr;
        *next_sorted_symbol_ptr-- = ranked_symbols_save;
      }
      else
        ranked_symbols_ptr--;
    }
  }

  for (i1 = 1 ; i1 < num_regular_definitions ; i1++) {
    U32 temp_symbol = ranked_symbols[i1];
    U32 temp_symbol_count = sd[temp_symbol].count;
    if (temp_symbol_count > sd[ranked_symbols[i1-1]].count) {
      i2 = i1 - 1;
      ranked_symbols[i1] = ranked_symbols[i2];
      while (i2 && (temp_symbol_count > sd[ranked_symbols[i2-1]].count)) {
        ranked_symbols[i2] = ranked_symbols[i2-1];
        i2--;
      }
      ranked_symbols[i2] = temp_symbol;
    }
  }

  mtfg_queue_8_offset = 0;
  mtfg_queue_16_offset = 0;
  mtfg_queue_32_offset = 0;
  mtfg_queue_64_offset = 0;
  mtfg_queue_128_offset = 0;
  mtfg_queue_192_offset = 0;
  for (i1 = 0 ; i1 < 8 ; i1++)
    mtfg_queue_0[i1] = end_symbols;
  for (i1 = 0 ; i1 < 8 ; i1++)
    mtfg_queue_8[i1] = end_symbols;
  for (i1 = 0 ; i1 < 16 ; i1++)
    mtfg_queue_16[i1] = end_symbols;
  for (i1 = 0 ; i1 < 32 ; i1++)
    mtfg_queue_32[i1] = end_symbols;
  for (i1 = 0 ; i1 < 64 ; i1++)
    mtfg_queue_64[i1] = end_symbols;
  for (i1 = 0 ; i1 < 64 ; i1++)
    mtfg_queue_128[i1] = end_symbols;
  for (i1 = 0 ; i1 < 64 ; i1++)
    mtfg_queue_192[i1] = end_symbols;

  for (i1=2 ; i1 <= MAX_INSTANCES_FOR_MTF_QUEUE ; i1++) { /* PUT i1=2 OUTSIDE OF LOOP */
    mtf_queue_hits = 0;
    for (i2=1 ; i2 <= MTF_QUEUE_SIZE ; i2++)
      mtf_queue_hits += mtf_queue_hit_count[i1][i2];
    if (mtf_queue_peak[i1] > MTF_QUEUE_SIZE) {
      if (i1 != 2) {
        if (use_mtf)
          mtf_queue_overflow_code_length[i1] = (U32)(0.3 + log2((double)num_symbols_to_code / (double)(i1-1)
              * (double)i1 / (double)(i1+1)
              * (double)((mtf_queue_peak[i1] - MTF_QUEUE_SIZE) * (i1-1)) / (double)(mtf_queue_started[i1]*(i1-1) - mtf_queue_hits)
              * 0.5 * (1.0 + (double)((mtf_queue_peak[i1] - MTF_QUEUE_SIZE) * (i1-1))
                / (double)(mtf_queue_started[i1] * (i1-1) - mtf_queue_hits))));
        else
          mtf_queue_overflow_code_length[i1] = (U32)(0.6 + log2((double)num_symbols_to_code / (double)(i1-1)
              * (double)i1 / (double)(i1+1) * (double)(mtf_queue_peak[i1] * (i1-1)) / (double)(mtf_queue_started[i1] * (i1-1))));
        if (mtf_queue_overflow_code_length[i1] > mtf_queue_overflow_code_length[i1-1])
          mtf_queue_overflow_code_length[i1] = mtf_queue_overflow_code_length[i1-1];
        else if (mtf_queue_overflow_code_length[i1] < mtf_queue_overflow_code_length[i1-1] - 1)
          mtf_queue_overflow_code_length[i1] = mtf_queue_overflow_code_length[i1-1] - 1;
      }
      else {
        if (use_mtf) {
          mtf_queue_overflow_code_length[2] = (U32)(0.3 + log2((double)num_symbols_to_code
              * (double)(mtf_queue_peak[2] - MTF_QUEUE_SIZE) / (double)(mtf_queue_started[2] - mtf_queue_hits)
              * 0.5 * (1.0 + (double)(mtf_queue_peak[2] - MTF_QUEUE_SIZE) / (double)(mtf_queue_started[2] - mtf_queue_hits))));
          if (mtf_queue_overflow_code_length[2] > 25)
            mtf_queue_overflow_code_length[2] = 25;
        }
        else {
          mtf_queue_overflow_code_length[2] = (U32)(0.3 + log2((double)num_symbols_to_code
              * (double)mtf_queue_peak[2] / (double)mtf_queue_started[2]));
          if (mtf_queue_overflow_code_length[2] > 25)
            mtf_queue_overflow_code_length[2] = 25;
        }
      }
    }
    else if (i1 == 2) {
      if (mtf_queue_started[2]) {
        mtf_queue_overflow_code_length[2] = (U32)(0.3 + log2((double)num_symbols_to_code
            * (double)mtf_queue_peak[2] / (double)mtf_queue_started[2]));
        if (mtf_queue_overflow_code_length[2] > 25)
          mtf_queue_overflow_code_length[2] = 25;
      }
      else
        mtf_queue_overflow_code_length[2] = 25;
    }
    else {
      if (mtf_queue_started[i1] && (use_mtf == 0)) {
        mtf_queue_overflow_code_length[i1] = (U32)(0.6 + log2((double)num_symbols_to_code / (double)(i1-1)
            * (double)i1 / (double)(i1+1)
            * (double)(mtf_queue_peak[i1]*(i1-1)) / (double)(mtf_queue_started[i1]*(i1-1))));
        if (mtf_queue_overflow_code_length[i1] > mtf_queue_overflow_code_length[i1-1])
          mtf_queue_overflow_code_length[i1] = mtf_queue_overflow_code_length[i1-1];
        else if (mtf_queue_overflow_code_length[i1] < mtf_queue_overflow_code_length[i1-1] - 1)
          mtf_queue_overflow_code_length[i1] = mtf_queue_overflow_code_length[i1-1] - 1;
      }
      else
        mtf_queue_overflow_code_length[i1] = mtf_queue_overflow_code_length[i1-1];
    }
  }
  max_code_length = mtf_queue_overflow_code_length[2];

  if (use_mtf) {
    mtf_queue_miss_code_space = 0;
    mtf_overflow_symbols_to_code = 0;
    for (i1 = 2 ; i1 <= MAX_INSTANCES_FOR_MTF_QUEUE ; i1++) {
      if (mtf_queue_peak[i1] > MTF_QUEUE_SIZE)
        mtf_queue_miss_code_space += (1 << (30 - mtf_queue_overflow_code_length[i1])) * (mtf_queue_peak[i1] - MTF_QUEUE_SIZE);
      mtf_overflow_symbols_to_code += (i1-1) * mtf_queue_started[i1];
      mtf_queue_size[i1] = 0;
    }
  }
  else {
    mtf_queue_miss_code_space = 0;
    mtf_overflow_symbols_to_code = 0;
    for (i1 = 2 ; i1 <= MAX_INSTANCES_FOR_MTF_QUEUE ; i1++) {
      mtf_queue_miss_code_space += (1 << (30 - mtf_queue_overflow_code_length[i1])) * mtf_queue_peak[i1];
      mtf_overflow_symbols_to_code += (i1-1) * mtf_queue_started[i1];
    }
  }

  // Recalculate code lengths knowing how many symbols are needed for 2 - 15 instance symbols that fall out of mtf queues
  num_define_symbols_written = 0;
  remaining_symbols_to_code = num_symbols_to_code - mtf_overflow_symbols_to_code - num_symbols_defined - mtfg_symbols_reduced;
  remaining_code_space = (1 << 30);
  remaining_code_space -= 1 << (30 - max_code_length); // reserve space for EOF
  remaining_code_space -= 0x02000000; // reserve code space for define symbols so they don't get too long
  remaining_code_space -= mtf_queue_miss_code_space; // reserve code space for symbols that overflow mtf queues
  remaining_code_space += remaining_code_space >> 5;
  remaining_symbols_to_code += remaining_symbols_to_code >> 5;
  max_regular_code_length = 1;

  prior_inst = 0;
  for (i1=0 ; i1<num_definitions_to_code ; i1++) {
    sd[ranked_symbols[i1]].type &= 0xF7;
    symbol_inst = sd[ranked_symbols[i1]].count;
    if (symbol_inst <= MAX_INSTANCES_FOR_MTF_QUEUE) {
      symbol_code_length = mtf_queue_overflow_code_length[symbol_inst];
      sd[ranked_symbols[i1]].code_length = symbol_code_length;
    }
    else {
      num_regular_definitions--;
      d_remaining_symbols_to_code = (double)remaining_symbols_to_code;
      if (--symbol_inst != prior_inst) {
        prior_inst = symbol_inst;
        symbol_inst_factor = 1.4 * (double)0x40000000 / (double)symbol_inst;
      }
      symbol_code_length = (U8)(log2(d_remaining_symbols_to_code * symbol_inst_factor / (double)(remaining_code_space - 0x20)));
      if (symbol_code_length < 2) // limit so files with less than 2 bit symbols (ideally) work
        symbol_code_length = 2;
      else if (i1 && (symbol_code_length < sd[ranked_symbols[0]].code_length))
        symbol_code_length = sd[ranked_symbols[0]].code_length;
      else if (symbol_code_length > 24)
        symbol_code_length = 24;
      while (remaining_code_space - (1 << (30 - symbol_code_length))
          < (S32)(num_regular_definitions * (0x40000000 >> (max_code_length - 1))))
        symbol_code_length++;
      if (symbol_code_length > max_regular_code_length)
        max_regular_code_length = symbol_code_length;
      if (symbol_code_length < 11)
        sd[ranked_symbols[i1]].type &= 0xFB;
      sd[ranked_symbols[i1]].code_length = symbol_code_length;
      remaining_code_space -= (1 << (30 - symbol_code_length));
      remaining_symbols_to_code -= symbol_inst;
    }
  }
  if (verbose) {
    if (verbose == 1) {
      for (i1 = 0 ; i1 < num_definitions_to_code ; i1++) {
        if ((sd[ranked_symbols[i1]].code_length >= 11)
            && (sd[ranked_symbols[i1]].inst_found > MAX_INSTANCES_FOR_MTF_QUEUE))
          printf("%u: #%u %u L%u D%02x: \"",(unsigned int)i1,(unsigned int)sd[ranked_symbols[i1]].inst_found,
              (unsigned int)sd[ranked_symbols[i1]].count,(unsigned int)sd[ranked_symbols[i1]].code_length,
              (unsigned int)sd[ranked_symbols[i1]].type & 0xF4);
        else
          printf("%u: #%u L%u: \"",(unsigned int)i1,(unsigned int)sd[ranked_symbols[i1]].inst_found,
              (unsigned int)sd[ranked_symbols[i1]].code_length);
        print_string(ranked_symbols[i1]);
        printf("\"\n");
      }
    }
    else {
      U32 symbol_limit = num_definitions_to_code;
      for (i1 = 0 ; i1 < symbol_limit ; i1++) {
        if (sd[i1].inst_found == 0)
          symbol_limit++;
        else {
          if ((sd[i1].code_length >= 11) && (sd[i1].inst_found > MAX_INSTANCES_FOR_MTF_QUEUE))
            printf("%u: #%u %u L%u D%02x: \"",(unsigned int)i1,(unsigned int)sd[i1].inst_found,
                (unsigned int)sd[i1].count,(unsigned int)sd[i1].code_length,(unsigned int)sd[i1].type & 0xF4);
          else
            printf("%u: #%u L%u: \"",(unsigned int)i1,(unsigned int)sd[i1].inst_found,(unsigned int)sd[i1].code_length);
          print_string(i1);
          printf("\"\n");
        }
      }
    }
  }
  if (num_definitions_to_code == 0) {
    max_regular_code_length = 24;
    sd[ranked_symbols[0]].code_length = 25;
  }
  else if (sd[ranked_symbols[0]].count <= MAX_INSTANCES_FOR_MTF_QUEUE)
    max_regular_code_length = sd[ranked_symbols[0]].code_length - 1;

  sd[end_symbols].type = 0;
  i1 = 0;
  while ((sd[ranked_symbols[i1]].count > MAX_INSTANCES_FOR_MTF_QUEUE) && (i1 < num_definitions_to_code)) {
    if ((sd[ranked_symbols[i1]].count) && (sd[ranked_symbols[i1]].type & 0x20)) {
      if (sd[ranked_symbols[i1]].space_score > 0)
        sd[ranked_symbols[i1]].type |= 0xC0;
      else
        sd[ranked_symbols[i1]].type |= 0x40;
    }
    i1++;
  }

  for (i1 = start_my_symbols ; i1 < end_symbols; i1++)
    if (sd[i1].type & 0x40) {
      U32 last_symbol = symbol[sd[i1 + 1].define_symbol_start_index - 2];
      while (last_symbol >= start_my_symbols) {
        if (sd[last_symbol].type & 0x80) {
          sd[i1].type &= 0x3F;
          break;
        }
        last_symbol = symbol[sd[last_symbol + 1].define_symbol_start_index - 2];
      }
    }

  if((fd_out = fopen(argv[arg_num],"wb")) == NULL) {
    printf("fopen error - file '%s' not found\n",argv[arg_num]);
    exit(0);
  }

  for (i1=0 ; i1<end_symbols ; i1++)
    sd[i1].inst_found = 0;
  symbol_ptr = symbol;
  prior_is_cap = 0;
  InitEncoder(fd_out, MAX_INSTANCES_FOR_MTF_QUEUE + (U32)(max_regular_code_length - sd[ranked_symbols[0]].code_length) + 1);

  // HEADER:
  // BYTE 0:  7=cap_encoded, 6=UTF8_compliant, 5=use_mtf, 4-0=max_code_length-1
  // BYTE 1:  7=M4D, 6=M3D, 5=use_delta, 4-0=min_code_length-1
  // BYTE 2:  7=M7D, 6=M6D, 5=M5D, 4-0=max_code_length-max_regular_code_length
  // BYTE 3:  7=M15D, 6=M14D, 5=M13D, 4=M12D, 3=M11D, 2=M10D, 1=M9D, 0=M8D
  // if UTF8_compliant
  // BYTE 4:  7-5=unused, 4-0=base_bits
  // else if use_delta
  // BYTE 4:  7-6=unused, 5=little_endian, 4=offset delta, 3-2=log2_delta_bytes, 1-0=stride-1

  OutBuffer[OutCharNum++] = (cap_encoded << 7) | (UTF8_compliant << 6) | (use_mtf << 5) | (mtf_queue_overflow_code_length[2] - 1);
  this_char = ((delta_format != 0) << 5) | sd[ranked_symbols[0]].code_length - 1;
  if (mtf_queue_overflow_code_length[3] != mtf_queue_overflow_code_length[2])
    this_char |= 0x40;
  if (mtf_queue_overflow_code_length[4] != mtf_queue_overflow_code_length[3])
    this_char |= 0x80;
  OutBuffer[OutCharNum++] = this_char;
  i1 = 7;
  do {
    this_char = (this_char << 1) | (mtf_queue_overflow_code_length[i1] != mtf_queue_overflow_code_length[i1-1]);
  } while (--i1 != 4);
  OutBuffer[OutCharNum++] = (this_char << 5) | (mtf_queue_overflow_code_length[2] - max_regular_code_length);
  i1 = 15;
  do {
    this_char = (this_char << 1) | (mtf_queue_overflow_code_length[i1] != mtf_queue_overflow_code_length[i1-1]);
  } while (--i1 != 7);
  OutBuffer[OutCharNum++] = this_char;
  if (UTF8_compliant)
    OutBuffer[OutCharNum++] = base_bits;
  else if (delta_format)
    OutBuffer[OutCharNum++] = ((delta_format & 0xF8) >> 1) + (delta_format & 7) - 1;

  i1 = 0xFF;
  if (UTF8_compliant)
    i1 = 0x80;
  do {
    for (i2 = 2 ; i2 <= max_code_length ; i2++) {
      sym_list_bits[i1][i2] = 2;
      if (0 == (sym_list_ptrs[i1][i2] = (U32 *)malloc(sizeof(U32) * 4))) {
        fprintf(stderr,"FATAL ERROR - symbol list malloc failure\n"); \
        exit(0);
      }
      nsob[i1][i2] = 0;
      nbob[i1][i2] = 0;
      fbob[i1][i2] = 0;
    }
    sum_nbob[i1] = 0;
    nbob_shift[i1] = max_code_length - 12;
  } while (i1--);
  found_first_symbol = 0;
  prior_end = 0;
  num_grammar_rules = 1;

  fprintf(stderr,"\nuse_mtf %u, mcl %u mrcl %u \n",
      (unsigned int)use_mtf,(unsigned int)max_code_length,(unsigned int)max_regular_code_length);

  if (UTF8_compliant || cap_encoded) {
    cap_symbol_defined = 0;
    cap_lock_symbol_defined = 0;
    while (symbol_ptr < first_define_ptr) {
      this_symbol = *symbol_ptr++;
      this_symbol_count = sd[this_symbol].count;
      symbol_inst = sd[this_symbol].inst_found++;
      if (symbol_inst == 0) {
        embed_define(this_symbol, 0);
      }
      else if (this_symbol_count <= MAX_INSTANCES_FOR_MTF_QUEUE) {
        if (use_mtf) {
          manage_mtf_queue(this_symbol,symbol_inst,this_symbol_count,0);
        }
        else {
          manage_mtf_symbol(this_symbol,symbol_inst,this_symbol_count,0);
        }
        prior_symbol = this_symbol;
      }
      else {
        if (sd[this_symbol].type & 8) {
          if (prior_is_cap == 0) {
            manage_mtfg_queue(this_symbol,0);
          }
          else {
            manage_mtfg_queue_prior_cap(this_symbol,0);
          }
          prior_is_cap = cap_encoded & sd[this_symbol].type;
        }
        else {
          CodeLength = sd[this_symbol].code_length;
          if (prior_is_cap == 0) {
            EncodeDictType(LEVEL0);
            prior_is_cap = cap_encoded & sd[this_symbol].type;
          }
          else {
            EncodeDictType(LEVEL0_CAP);
            prior_is_cap = sd[this_symbol].type & 1;
          }
          encode_dictionary_symbol(this_symbol);
          if (sd[this_symbol].type & 4)
            add_symbol_to_mtfg_queue(this_symbol);
        }
        prior_symbol = this_symbol;
      }
      prior_end = sd[this_symbol].ends;
      if (((symbol_ptr-symbol)&0x1FFFFF) == 0)
        fprintf(stderr,"Encoded %u of %u level 1 symbols\r",
            (unsigned int)(symbol_ptr - symbol),(unsigned int)(first_define_ptr - symbol));
    }
  }
  else {
    while (symbol_ptr < first_define_ptr) {
      this_symbol = *symbol_ptr++;
      this_symbol_count = sd[this_symbol].count;
      symbol_inst = sd[this_symbol].inst_found++;
      if (symbol_inst == 0) {
        embed_define_binary(this_symbol, 0);
      }
      else if (this_symbol_count <= MAX_INSTANCES_FOR_MTF_QUEUE) {
        if (use_mtf) {
          manage_mtf_queue(this_symbol,symbol_inst,this_symbol_count,0);
        }
        else {
          manage_mtf_symbol(this_symbol,symbol_inst,this_symbol_count,0);
        }
      }
      else {
        if (sd[this_symbol].type & 8) {
          if (prior_is_cap == 0) {
            manage_mtfg_queue(this_symbol,0);
          }
          else {
            manage_mtfg_queue_prior_cap(this_symbol,0);
          }
        }
        else {
          CodeLength = sd[this_symbol].code_length;
          EncodeDictType(LEVEL0);
          encode_dictionary_symbol(this_symbol);
          if (sd[this_symbol].type & 4)
            add_symbol_to_mtfg_queue(this_symbol);
        }
      }
      prior_end = sd[this_symbol].ends;
      if (((symbol_ptr-symbol)&0x1FFFFF) == 0)
        fprintf(stderr,"Encoded %u of %u level 1 symbols\r",
            (unsigned int)(symbol_ptr - symbol),(unsigned int)(first_define_ptr - symbol));
    }
  }


  // send EOF and flush output
  Symbol = end_symbol;
  CodeLength = max_code_length - nbob_shift[Symbol];
  DictionaryBins = sum_nbob[Symbol];
  BinNum = fbob[Symbol][max_code_length];
  if (prior_is_cap == 0) {
    EncodeDictType(LEVEL0);
  }
  else {
    EncodeDictType(LEVEL0_CAP);
  }
  if (cap_encoded) {
    if (max_code_length >= 14) {
      if (sd[prior_symbol].type & 0x20) {
        if (sd[prior_symbol].type & 0x80) {
          EncodeFirstChar(2, prior_end);
        }
        else if (sd[prior_symbol].type & 0x40) {
          EncodeFirstChar(3, prior_end);
        }
        else {
          EncodeFirstChar(1, prior_end);
        }
      }
      else {
        EncodeFirstChar(0, prior_end);
      }
    }
    else {
      EncodeFirstChar(0, prior_end);
    }
  }
  else if (UTF8_compliant) {
    EncodeFirstChar(0, prior_end);
  }
  else {
    EncodeFirstCharBinary(prior_end);
  }
  if (max_code_length - nbob_shift[Symbol] > 12) {
    BinCode = 0;
    EncodeLongDictionarySymbol(1);
  }
  else {
    EncodeShortDictionarySymbol(CodeLength, 1);
  }
  FinishEncoder();
  fprintf(stderr,"Encoded %u level 1 symbols             \n",(unsigned int)(symbol_ptr - symbol));
  fprintf(stderr,"Reduced %u grammar rules\n",rules_reduced);
  grammar_size -= 2 * rules_reduced;
  fprintf(stderr,"Compressed file size: %u bytes.  %u grammar rules.  Grammar size: %u symbols\n",
      (unsigned int)ftell(fd_out),(unsigned int)num_grammar_rules,(unsigned int)grammar_size);
  fclose(fd_out);
  i1 = 0xFF;
  if (UTF8_compliant)
    i1 = 0x80;
  do {
    for (i2 = 2 ; i2 <= max_code_length ; i2++)
      free(sym_list_ptrs[i1][i2]);
  } while (i1--);
  fprintf(stderr,"Grammar encoding time = %.3f seconds.\n",(float)(clock()-start_time)/CLOCKS_PER_SEC);
  return(0);
}