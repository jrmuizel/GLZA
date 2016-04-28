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

// GLZAencode.c
//   Encodes files created by GLZAcompress
//
// Usage:
//   GLZAencode <infilename> <outfilename>


#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
const unsigned int CAP_CHAR = 0x43;
const unsigned char INSERT_SYMBOL_CHAR = 0xFE;
const unsigned char DEFINE_SYMBOL_CHAR = 0xFF;
const unsigned int UNIQUE_CHAR = 0x7FFFFFFF;
const unsigned int START_UTF8_2BYTE_SYMBOLS = 0x80;
const unsigned int START_UTF8_3BYTE_SYMBOLS = 0x800;
const unsigned int START_UTF8_4BYTE_SYMBOLS = 0x10000;
const unsigned int START_MY_SYMBOLS = 0x00080000;
const unsigned int READ_SIZE = 16000000;
const unsigned int MAX_FILE_SYMBOLS = 220000000;
const unsigned int ESTIMATED_MTF_QUEUE_SPACE = 0x06000000;
const unsigned int MAX_SYMBOLS_DEFINED = 0x00A00000;
const unsigned char MAX_BITS_IN_CODE = 25;
const unsigned int MAX_INSTANCES_FOR_MTF_QUEUE = 20;
const unsigned int MTF_QUEUE_LENGTH = 64;

unsigned char UTF8_compliant, base_bits, cap_encoded, prior_is_cap, use_mtf;
unsigned char in_data[16000003], symbol_is_nonergodic[0x00A00000];
unsigned char symbol_lengths[0x00A00000], symbol_starts_az[0x00A00000], symbol_ends_cap[0x00A00000];
unsigned char *in_char_ptr, *end_char_ptr;

unsigned int num_define_symbols_written, num_regular_definitions;
unsigned int num_symbols_to_code, mtf_overflow_symbols_to_code;
unsigned int max_code_length, max_regular_code_length, mtf_queue_miss_code_space;
unsigned int symbol_code_length, symbol_bits, symbol_index, symbol_to_move, table_index;
unsigned int dictionary_bins, dictionary_bins_cap, min_extra_reduce_index;
unsigned int symbol[220000000],symbol_count[0x00A00000], orig_symbol_count[0x00A00000], symbol_inst_found[0x00A00000];
unsigned int sorted_symbols[0x00A00000], mtfg_hits[0x00A00000], mtfg_hits2[0x00A00000], *define_symbol_start_ptr[0x00A00000];
unsigned int symbol_array_index[0x00A00000], symbol_array_index_cap[0x00A00000];
unsigned int mtf_queue[21][65], mtf_queue_hit_count[21][65];
unsigned int mtf_queue_started[21], mtf_queue_done[21], mtf_queue_peak[21], mtf_queue_size[21];
unsigned int mtf_queue_overflow_code_length[21];
unsigned int num_symbols_of_bits[26], num_symbols_of_bits_cap[26], num_bins_of_bits[26], num_bins_of_bits_cap[26];
unsigned int first_bin_of_bits[26], first_bin_of_bits_cap[26];
unsigned int symbol_array_of_bits[26][4000000], symbol_array_of_bits_cap[26][2000000];
unsigned int mtfg_queue_0[8], mtfg_queue_8[8], mtfg_queue_16[0x10], mtfg_queue_32[0x20];
unsigned int mtfg_queue_64[0x40], mtfg_queue_128[0x40], mtfg_queue_192[0x40];
unsigned int mtfg_queue_8_offset, mtfg_queue_16_offset, mtfg_queue_32_offset;
unsigned int mtfg_queue_64_offset, mtfg_queue_128_offset, mtfg_queue_192_offset;
unsigned int *mtf_queue_ptr, *mtf_queue_end_ptr;
unsigned int *symbol_ptr, *first_define_ptr = 0;

#include "GLZAmodel.h"




void print_string(unsigned int string_number) {
  unsigned int *symbol_ptr, *next_symbol_ptr;
  if (string_number < START_MY_SYMBOLS) {
    if (UTF8_compliant) {
      if (string_number < START_UTF8_2BYTE_SYMBOLS)
        printf("%c",string_number);
      else if (string_number < START_UTF8_3BYTE_SYMBOLS) {
        printf("%c",(unsigned char)(string_number >> 6) + 0xC0);
        printf("%c",(unsigned char)(string_number & 0x3F) + 0x80);
      }
      else if (string_number < START_UTF8_4BYTE_SYMBOLS) {
        printf("%c",(unsigned char)(string_number >> 12) + 0xE0);
        printf("%c",(unsigned char)((string_number >> 6) & 0x3F) + 0x80);
        printf("%c",(unsigned char)(string_number & 0x3F) + 0x80);
      }
      else {
        printf("%c",(unsigned char)(string_number >> 18) + 0xF0);
        printf("%c",(unsigned char)((string_number >> 12) & 0x3F) + 0x80);
        printf("%c",(unsigned char)((string_number >> 6) & 0x3F) + 0x80);
        printf("%c",(unsigned char)(string_number & 0x3F) + 0x80);
      }
    }
    else
      printf("%c",string_number);
  }
  else {
    symbol_ptr = define_symbol_start_ptr[string_number-START_MY_SYMBOLS];
    next_symbol_ptr = define_symbol_start_ptr[string_number-START_MY_SYMBOLS+1] - 1;
    while (symbol_ptr != next_symbol_ptr)
      print_string(*symbol_ptr++);
  }
}


#define remove_mtfg_queue_symbol_16() { \
  unsigned int qp = mtfg_queue_position - 16; \
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
  *(mtfg_queue_192 + mtfg_queue_192_offset) = 0x9FFFFF; \
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F; \
}


#define remove_mtfg_queue_symbol_32() { \
  unsigned int qp = mtfg_queue_position - 32; \
  while (qp != 31) { \
    *(mtfg_queue_32 + ((mtfg_queue_32_offset + qp) & 0x1F)) = *(mtfg_queue_32 + ((mtfg_queue_32_offset + qp + 1) & 0x1F)); \
    qp++; \
  } \
  *(mtfg_queue_32 + ((mtfg_queue_32_offset - 1) & 0x1F)) = *(mtfg_queue_64 + mtfg_queue_64_offset); \
  *(mtfg_queue_64 + mtfg_queue_64_offset) = *(mtfg_queue_128 + mtfg_queue_128_offset); \
  mtfg_queue_64_offset = (mtfg_queue_64_offset + 1) & 0x3F; \
  *(mtfg_queue_128 + mtfg_queue_128_offset) = *(mtfg_queue_192 + mtfg_queue_192_offset); \
  mtfg_queue_128_offset = (mtfg_queue_128_offset + 1) & 0x3F; \
  *(mtfg_queue_192 + mtfg_queue_192_offset) = 0x9FFFFF; \
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F; \
}


#define remove_mtfg_queue_symbol_64() { \
  unsigned int qp = mtfg_queue_position - 64; \
  while (qp != 63) { \
    *(mtfg_queue_64 + ((mtfg_queue_64_offset + qp) & 0x3F)) = *(mtfg_queue_64 + ((mtfg_queue_64_offset + qp + 1) & 0x3F)); \
    qp++; \
  } \
  *(mtfg_queue_64 + ((mtfg_queue_64_offset - 1) & 0x3F)) = *(mtfg_queue_128 + mtfg_queue_128_offset); \
  *(mtfg_queue_128 + mtfg_queue_128_offset) = *(mtfg_queue_192 + mtfg_queue_192_offset); \
  mtfg_queue_128_offset = (mtfg_queue_128_offset + 1) & 0x3F; \
  *(mtfg_queue_192 + mtfg_queue_192_offset) = 0x9FFFFF; \
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F; \
}


#define remove_mtfg_queue_symbol_128() { \
  unsigned int qp = mtfg_queue_position - 128; \
  while (qp != 63) { \
    *(mtfg_queue_128 + ((mtfg_queue_128_offset + qp) & 0x3F)) \
        = *(mtfg_queue_128 + ((mtfg_queue_128_offset + qp + 1) & 0x3F)); \
    qp++; \
  } \
  *(mtfg_queue_128 + ((mtfg_queue_128_offset - 1) & 0x3F)) = *(mtfg_queue_192 + mtfg_queue_192_offset); \
  *(mtfg_queue_192 + mtfg_queue_192_offset) = 0x9FFFFF; \
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F; \
}


#define remove_mtfg_queue_symbol_192() { \
  unsigned int qp = mtfg_queue_position - 192; \
  while (qp != 63) { \
    *(mtfg_queue_192 + ((mtfg_queue_192_offset + qp) & 0x3F)) \
        = *(mtfg_queue_192 + ((mtfg_queue_192_offset + qp + 1) & 0x3F)); \
    qp++; \
  } \
  *(mtfg_queue_192 + ((mtfg_queue_192_offset + qp) & 0x3F)) = 0x9FFFFF; \
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
  symbol_is_nonergodic[*(mtfg_queue_192 + mtfg_queue_192_offset)] &= 1; \
  *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191; \
}


#define add_symbol_to_mtfg_queue(symbol_number) { \
  symbol_is_nonergodic[symbol_number] |= 2; \
  unsigned int mtfg_queue_symbol_7, mtfg_queue_symbol_15; \
  increment_mtfg_queue_0(symbol_number); \
  increment_mtfg_queue_8(); \
  if (symbol_lengths[mtfg_queue_symbol_15] > 12) { \
    unsigned int mtfg_queue_symbol_31; \
    increment_mtfg_queue_16(); \
    if (symbol_lengths[mtfg_queue_symbol_31] != 13) { \
      unsigned int mtfg_queue_symbol_63; \
      increment_mtfg_queue_32(); \
      if (symbol_lengths[mtfg_queue_symbol_63] != 14) { \
        unsigned int mtfg_queue_symbol_127; \
        increment_mtfg_queue_64(); \
        if (symbol_lengths[mtfg_queue_symbol_127] != 15) { \
          unsigned int mtfg_queue_symbol_191; \
          increment_mtfg_queue_128(); \
          if (symbol_lengths[mtfg_queue_symbol_191] != 16) { \
            increment_mtfg_queue_192(); \
          } \
          else \
            symbol_is_nonergodic[mtfg_queue_symbol_191] &= 1; \
        } \
        else \
          symbol_is_nonergodic[mtfg_queue_symbol_127] &= 1; \
      } \
      else \
        symbol_is_nonergodic[mtfg_queue_symbol_63] &= 1; \
    } \
    else \
      symbol_is_nonergodic[mtfg_queue_symbol_31] &= 1; \
  } \
  else \
    symbol_is_nonergodic[mtfg_queue_symbol_15] &= 1; \
}


#define manage_mtfg_queue1(symbol_number) { \
  unsigned int mtfg_queue_position; \
  unsigned int i4; \
  mtfg_queue_position = 0; \
  do { \
    if (symbol_number == mtfg_queue_0[mtfg_queue_position]) { \
      mtfg_hits2[symbol_number] += 14; \
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
        mtfg_hits2[symbol_number] += 9; \
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
      mtfg_hits2[symbol_number] += 5; \
      unsigned int mtfg_queue_symbol_7; \
      increment_mtfg_queue_0(symbol_number); \
      do { \
        if (symbol_number == *(mtfg_queue_8 + ((mtfg_queue_position + mtfg_queue_8_offset) & 7))) { \
          i4 = mtfg_queue_position - 8; \
          while (i4) { \
            *(mtfg_queue_8 + ((mtfg_queue_8_offset + i4) & 7)) \
                = *(mtfg_queue_8 + ((mtfg_queue_8_offset + i4 - 1) & 7)); \
            i4--; \
          } \
          *(mtfg_queue_8 + mtfg_queue_8_offset) = mtfg_queue_symbol_7; \
          break; \
        } \
        mtfg_queue_position++; \
      } while (mtfg_queue_position != 16); \
      if (mtfg_queue_position == 16) { \
        mtfg_hits2[symbol_number]+= 3; \
        unsigned int mtfg_queue_symbol_15; \
        increment_mtfg_queue_8(); \
        do { \
          if (symbol_number == *(mtfg_queue_16 + ((mtfg_queue_position + mtfg_queue_16_offset) & 0xF))) { \
            if (symbol_lengths[mtfg_queue_symbol_15] <= 12) { \
              symbol_is_nonergodic[mtfg_queue_symbol_15] &= 1; \
              remove_mtfg_queue_symbol_16(); \
            } \
            else { \
              i4 = mtfg_queue_position - 16; \
              while (i4) { \
                *(mtfg_queue_16 + ((mtfg_queue_16_offset + i4) & 0xF)) \
                    = *(mtfg_queue_16 + ((mtfg_queue_16_offset + i4 - 1) & 0xF)); \
                i4--; \
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
              mtfg_hits2[symbol_number]++; \
              if (symbol_lengths[mtfg_queue_symbol_15] <= 12) { \
                symbol_is_nonergodic[mtfg_queue_symbol_15] &= 1; \
                remove_mtfg_queue_symbol_32(); \
              } \
              else { \
                unsigned int mtfg_queue_symbol_31; \
                increment_mtfg_queue_16(); \
                if (symbol_lengths[mtfg_queue_symbol_31] == 13) \
                { \
                  symbol_is_nonergodic[mtfg_queue_symbol_31] &= 1; \
                  remove_mtfg_queue_symbol_32(); \
                } \
                else { \
                  i4 = mtfg_queue_position - 32; \
                  while (i4) { \
                    *(mtfg_queue_32 + ((mtfg_queue_32_offset + i4) & 0x1F)) \
                        = *(mtfg_queue_32 + ((mtfg_queue_32_offset + i4 - 1) & 0x1F)); \
                    i4--; \
                  } \
                  *(mtfg_queue_32 + mtfg_queue_32_offset) = mtfg_queue_symbol_31; \
                } \
              } \
              break; \
            } \
            mtfg_queue_position++; \
          } while (mtfg_queue_position != 64); \
          if (mtfg_queue_position == 64) { \
            do { \
              if (symbol_number == *(mtfg_queue_64 + ((mtfg_queue_position + mtfg_queue_64_offset) & 0x3F))) { \
                if (symbol_lengths[mtfg_queue_symbol_15] <= 12) { \
                  symbol_is_nonergodic[mtfg_queue_symbol_15] &= 1; \
                  remove_mtfg_queue_symbol_64(); \
                } \
                else { \
                  unsigned int mtfg_queue_symbol_31; \
                  increment_mtfg_queue_16(); \
                  if (symbol_lengths[mtfg_queue_symbol_31] == 13) { \
                    symbol_is_nonergodic[mtfg_queue_symbol_31] &= 1; \
                    remove_mtfg_queue_symbol_64(); \
                  } \
                  else { \
                    unsigned int mtfg_queue_symbol_63; \
                    increment_mtfg_queue_32(); \
                    if (symbol_lengths[mtfg_queue_symbol_63] == 14) { \
                      symbol_is_nonergodic[mtfg_queue_symbol_63] &= 1; \
                      remove_mtfg_queue_symbol_64(); \
                    } \
                    else { \
                      i4 = mtfg_queue_position - 64; \
                      while (i4) { \
                        *(mtfg_queue_64 + ((mtfg_queue_64_offset + i4) & 0x3F)) \
                            = *(mtfg_queue_64 + ((mtfg_queue_64_offset + i4 - 1) & 0x3F)); \
                        i4--; \
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
                  if (symbol_lengths[mtfg_queue_symbol_15] <= 12) { \
                    symbol_is_nonergodic[mtfg_queue_symbol_15] &= 1; \
                    remove_mtfg_queue_symbol_128(); \
                  } \
                  else { \
                    unsigned int mtfg_queue_symbol_31; \
                    increment_mtfg_queue_16(); \
                    if (symbol_lengths[mtfg_queue_symbol_31] == 13) { \
                      symbol_is_nonergodic[mtfg_queue_symbol_31] &= 1; \
                      remove_mtfg_queue_symbol_128(); \
                    } \
                    else { \
                      unsigned int mtfg_queue_symbol_63; \
                      increment_mtfg_queue_32(); \
                      if (symbol_lengths[mtfg_queue_symbol_63] == 14) { \
                        symbol_is_nonergodic[mtfg_queue_symbol_63] &= 1; \
                        remove_mtfg_queue_symbol_128(); \
                      } \
                      else { \
                        unsigned int mtfg_queue_symbol_127; \
                        increment_mtfg_queue_64(); \
                        if (symbol_lengths[mtfg_queue_symbol_127] == 15) { \
                          symbol_is_nonergodic[mtfg_queue_symbol_127] &= 1; \
                          remove_mtfg_queue_symbol_128(); \
                        } \
                        else { \
                          i4 = mtfg_queue_position - 128; \
                          while (i4) { \
                            *(mtfg_queue_128 + ((mtfg_queue_128_offset + i4) & 0x3F)) \
                                = *(mtfg_queue_128 + ((mtfg_queue_128_offset + i4 - 1) & 0x3F)); \
                            i4--; \
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
                if (symbol_lengths[mtfg_queue_symbol_15] <= 12) { \
                  symbol_is_nonergodic[mtfg_queue_symbol_15] &= 1; \
                  remove_mtfg_queue_symbol_192(); \
                } \
                else { \
                  unsigned int mtfg_queue_symbol_31; \
                  increment_mtfg_queue_16(); \
                  if (symbol_lengths[mtfg_queue_symbol_31] == 13) { \
                    symbol_is_nonergodic[mtfg_queue_symbol_31] &= 1; \
                    remove_mtfg_queue_symbol_192(); \
                  } \
                  else { \
                    unsigned int mtfg_queue_symbol_63; \
                    increment_mtfg_queue_32(); \
                    if (symbol_lengths[mtfg_queue_symbol_63] == 14) { \
                      symbol_is_nonergodic[mtfg_queue_symbol_63] &= 1; \
                      remove_mtfg_queue_symbol_192(); \
                    } \
                    else { \
                      unsigned int mtfg_queue_symbol_127; \
                      increment_mtfg_queue_64(); \
                      if (symbol_lengths[mtfg_queue_symbol_127] == 15) { \
                        symbol_is_nonergodic[mtfg_queue_symbol_127] &= 1; \
                        remove_mtfg_queue_symbol_192(); \
                      } \
                      else { \
                        unsigned int mtfg_queue_symbol_191; \
                        increment_mtfg_queue_128(); \
                        if (symbol_lengths[mtfg_queue_symbol_191] == 16) { \
                          symbol_is_nonergodic[mtfg_queue_symbol_191] &= 1; \
                          remove_mtfg_queue_symbol_192(); \
                        } \
                        else { \
                          i4 = mtfg_queue_position - 192; \
                          while (i4) { \
                            *(mtfg_queue_192 + ((mtfg_queue_192_offset + i4) & 0x3F)) \
                                = *(mtfg_queue_192 + ((mtfg_queue_192_offset + i4 - 1) & 0x3F)); \
                            i4--; \
                          } \
                          *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191; \
} } } } } } } } } } } } } \


#define manage_mtfg_queue(symbol_number, in_definition) { \
  unsigned int mtfg_queue_position = 0; \
  unsigned int cap_queue_position = 0; \
  unsigned int i4; \
  do { \
    if (symbol_number == mtfg_queue_0[mtfg_queue_position]) { \
      if (prior_is_cap == 0) { \
        if (in_definition == 0) { \
          EncodeMtfgType(LEVEL0); \
        } \
        else { \
          EncodeMtfgType(LEVEL1); \
        } \
        EncodeMtfgQueuePos(NOT_CAP); \
      } \
      else { \
        if (in_definition == 0) { \
          EncodeMtfgType(LEVEL0_CAP); \
        } \
        else { \
          EncodeMtfgType(LEVEL1_CAP); \
        } \
        unsigned int saved_qp = mtfg_queue_position; \
        mtfg_queue_position = cap_queue_position; \
        EncodeMtfgQueuePos(CAP); \
        mtfg_queue_position = saved_qp; \
      } \
      while (mtfg_queue_position) { \
        mtfg_queue_0[mtfg_queue_position] = mtfg_queue_0[mtfg_queue_position-1]; \
        mtfg_queue_position--; \
      } \
      mtfg_queue_0[0] = symbol_number; \
      break; \
    } \
    else if (symbol_starts_az[mtfg_queue_0[mtfg_queue_position]]) \
      cap_queue_position++; \
  } while (++mtfg_queue_position != 5); \
  if (mtfg_queue_position == 5) { \
    do { \
      if (symbol_number == mtfg_queue_0[mtfg_queue_position]) { \
        if (prior_is_cap == 0) { \
          if (in_definition == 0) { \
            EncodeMtfgType(LEVEL0); \
          } \
          else { \
            EncodeMtfgType(LEVEL1); \
          } \
          EncodeMtfgQueuePos(NOT_CAP); \
        } \
        else { \
          if (in_definition == 0) { \
            EncodeMtfgType(LEVEL0_CAP); \
          } \
          else { \
            EncodeMtfgType(LEVEL1_CAP); \
          } \
          unsigned int saved_qp = mtfg_queue_position; \
          mtfg_queue_position = cap_queue_position; \
          EncodeMtfgQueuePos(CAP); \
          mtfg_queue_position = saved_qp; \
        } \
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
      else if (symbol_starts_az[mtfg_queue_0[mtfg_queue_position]]) \
        cap_queue_position++; \
    } while (++mtfg_queue_position != 8); \
    if (mtfg_queue_position == 8) { \
      unsigned int mtfg_queue_symbol_7; \
      increment_mtfg_queue_0(symbol_number); \
      do { \
        if (symbol_number == *(mtfg_queue_8 + ((mtfg_queue_position + mtfg_queue_8_offset) & 7))) { \
          if (prior_is_cap == 0) { \
            if (in_definition == 0) { \
              EncodeMtfgType(LEVEL0); \
            } \
            else { \
              EncodeMtfgType(LEVEL1); \
            } \
            EncodeMtfgQueuePos(NOT_CAP); \
          } \
          else { \
            if (in_definition == 0) { \
              EncodeMtfgType(LEVEL0_CAP); \
            } \
            else { \
              EncodeMtfgType(LEVEL1_CAP); \
            } \
            unsigned int saved_qp = mtfg_queue_position; \
            mtfg_queue_position = cap_queue_position; \
            EncodeMtfgQueuePos(CAP); \
            mtfg_queue_position = saved_qp; \
          } \
          i4 = mtfg_queue_position - 8; \
          while (i4) { \
            *(mtfg_queue_8 + ((mtfg_queue_8_offset + i4) & 7)) \
                = *(mtfg_queue_8 + ((mtfg_queue_8_offset + i4 - 1) & 7)); \
            i4--; \
          } \
          *(mtfg_queue_8 + mtfg_queue_8_offset) = mtfg_queue_symbol_7; \
          break; \
        } \
        else if (symbol_starts_az[*(mtfg_queue_8 + ((mtfg_queue_position + mtfg_queue_8_offset) & 7))]) \
          cap_queue_position++; \
      } while (++mtfg_queue_position != 16); \
      if (mtfg_queue_position == 16) { \
        unsigned int mtfg_queue_symbol_15; \
        increment_mtfg_queue_8(); \
        do { \
          if (symbol_number == *(mtfg_queue_16 + ((mtfg_queue_position + mtfg_queue_16_offset) & 0xF))) { \
            if (prior_is_cap == 0) { \
              if (in_definition == 0) { \
                EncodeMtfgType(LEVEL0); \
              } \
              else { \
                EncodeMtfgType(LEVEL1); \
              } \
              EncodeMtfgQueuePos(NOT_CAP); \
            } \
            else { \
              if (in_definition == 0) { \
                EncodeMtfgType(LEVEL0_CAP); \
              } \
              else { \
                EncodeMtfgType(LEVEL1_CAP); \
              } \
              unsigned int saved_qp = mtfg_queue_position; \
              mtfg_queue_position = cap_queue_position; \
              EncodeMtfgQueuePos(CAP); \
              mtfg_queue_position = saved_qp; \
            } \
            if (symbol_lengths[mtfg_queue_symbol_15] <= 12) { \
              symbol_is_nonergodic[mtfg_queue_symbol_15] &= 1; \
              remove_mtfg_queue_symbol_16(); \
            } \
            else { \
              i4 = mtfg_queue_position - 16; \
              while (i4) { \
                *(mtfg_queue_16 + ((mtfg_queue_16_offset + i4) & 0xF)) \
                    = *(mtfg_queue_16 + ((mtfg_queue_16_offset + i4 - 1) & 0xF)); \
                i4--; \
              } \
              *(mtfg_queue_16 + mtfg_queue_16_offset) = mtfg_queue_symbol_15; \
            } \
            break; \
          } \
          else if (symbol_starts_az[*(mtfg_queue_16 + ((mtfg_queue_position + mtfg_queue_16_offset) & 0xF))]) \
            cap_queue_position++; \
        } while (++mtfg_queue_position != 32); \
        if (mtfg_queue_position == 32) { \
          do { \
            if (symbol_number == *(mtfg_queue_32 + ((mtfg_queue_position + mtfg_queue_32_offset) & 0x1F))) { \
              if (prior_is_cap == 0) { \
                if (in_definition == 0) { \
                  EncodeMtfgType(LEVEL0); \
                } \
                else { \
                  EncodeMtfgType(LEVEL1); \
                } \
                EncodeMtfgQueuePos(NOT_CAP); \
              } \
              else { \
                if (in_definition == 0) { \
                  EncodeMtfgType(LEVEL0_CAP); \
                } \
                else { \
                  EncodeMtfgType(LEVEL1_CAP); \
                } \
                unsigned int saved_qp = mtfg_queue_position; \
                mtfg_queue_position = cap_queue_position; \
                EncodeMtfgQueuePos(CAP); \
                mtfg_queue_position = saved_qp; \
              } \
              if (symbol_lengths[mtfg_queue_symbol_15] <= 12) { \
                symbol_is_nonergodic[mtfg_queue_symbol_15] &= 1; \
                remove_mtfg_queue_symbol_32(); \
              } \
              else { \
                unsigned int mtfg_queue_symbol_31; \
                increment_mtfg_queue_16(); \
                if (symbol_lengths[mtfg_queue_symbol_31] == 13) { \
                  symbol_is_nonergodic[mtfg_queue_symbol_31] &= 1; \
                  remove_mtfg_queue_symbol_32(); \
                } \
                else { \
                  i4 = mtfg_queue_position - 32; \
                  while (i4) { \
                    *(mtfg_queue_32 + ((mtfg_queue_32_offset + i4) & 0x1F)) \
                        = *(mtfg_queue_32 + ((mtfg_queue_32_offset + i4 - 1) & 0x1F)); \
                    i4--; \
                  } \
                  *(mtfg_queue_32 + mtfg_queue_32_offset) = mtfg_queue_symbol_31; \
                } \
              } \
              break; \
            } \
            else if (symbol_starts_az[*(mtfg_queue_32 + ((mtfg_queue_position + mtfg_queue_32_offset) & 0x1F))]) \
              cap_queue_position++; \
          } while (++mtfg_queue_position != 64); \
          if (mtfg_queue_position == 64) { \
            do { \
              if (symbol_number == *(mtfg_queue_64 + ((mtfg_queue_position + mtfg_queue_64_offset) & 0x3F))) { \
                if (prior_is_cap == 0) { \
                  if (in_definition == 0) { \
                    EncodeMtfgType(LEVEL0); \
                  } \
                  else { \
                    EncodeMtfgType(LEVEL1); \
                  } \
                  EncodeMtfgQueuePos(NOT_CAP); \
                } \
                else { \
                  if (in_definition == 0) { \
                    EncodeMtfgType(LEVEL0_CAP); \
                  } \
                  else { \
                    EncodeMtfgType(LEVEL1_CAP); \
                  } \
                  unsigned int saved_qp = mtfg_queue_position; \
                  mtfg_queue_position = cap_queue_position; \
                  EncodeMtfgQueuePos(CAP); \
                  mtfg_queue_position = saved_qp; \
                } \
                if (symbol_lengths[mtfg_queue_symbol_15] <= 12) { \
                  symbol_is_nonergodic[mtfg_queue_symbol_15] &= 1; \
                  remove_mtfg_queue_symbol_64(); \
                } \
                else { \
                  unsigned int mtfg_queue_symbol_31; \
                  increment_mtfg_queue_16(); \
                  if (symbol_lengths[mtfg_queue_symbol_31] == 13) { \
                    symbol_is_nonergodic[mtfg_queue_symbol_31] &= 1; \
                    remove_mtfg_queue_symbol_64(); \
                  } \
                  else { \
                    unsigned int mtfg_queue_symbol_63; \
                    increment_mtfg_queue_32(); \
                    if (symbol_lengths[mtfg_queue_symbol_63] == 14) { \
                      symbol_is_nonergodic[mtfg_queue_symbol_63] &= 1; \
                      remove_mtfg_queue_symbol_64(); \
                    } \
                    else { \
                      i4 = mtfg_queue_position - 64; \
                      while (i4) { \
                        *(mtfg_queue_64 + ((mtfg_queue_64_offset + i4) & 0x3F)) \
                            = *(mtfg_queue_64 + ((mtfg_queue_64_offset + i4 - 1) & 0x3F)); \
                        i4--; \
                      } \
                      *(mtfg_queue_64 + mtfg_queue_64_offset) = mtfg_queue_symbol_63; \
                    } \
                  } \
                } \
                break; \
              } \
              else if (symbol_starts_az[*(mtfg_queue_64 + ((mtfg_queue_position + mtfg_queue_64_offset) & 0x3F))]) \
                cap_queue_position++; \
            } while (++mtfg_queue_position != 128); \
            if (mtfg_queue_position == 128) { \
              do { \
                if (symbol_number == *(mtfg_queue_128 + ((mtfg_queue_position + mtfg_queue_128_offset) & 0x3F))) { \
                  if (prior_is_cap == 0) { \
                    if (in_definition == 0) { \
                      EncodeMtfgType(LEVEL0); \
                    } \
                    else { \
                      EncodeMtfgType(LEVEL1); \
                    } \
                    EncodeMtfgQueuePos(NOT_CAP); \
                  } \
                  else { \
                    if (in_definition == 0) { \
                      EncodeMtfgType(LEVEL0_CAP); \
                    } \
                    else { \
                      EncodeMtfgType(LEVEL1_CAP); \
                    } \
                    unsigned int saved_qp = mtfg_queue_position; \
                    mtfg_queue_position = cap_queue_position; \
                    EncodeMtfgQueuePos(CAP); \
                    mtfg_queue_position = saved_qp; \
                  } \
                  if (symbol_lengths[mtfg_queue_symbol_15] <= 12) { \
                    symbol_is_nonergodic[mtfg_queue_symbol_15] &= 1; \
                    remove_mtfg_queue_symbol_128(); \
                  } \
                  else { \
                    unsigned int mtfg_queue_symbol_31; \
                    increment_mtfg_queue_16(); \
                    if (symbol_lengths[mtfg_queue_symbol_31] == 13) { \
                      symbol_is_nonergodic[mtfg_queue_symbol_31] &= 1; \
                      remove_mtfg_queue_symbol_128(); \
                    } \
                    else { \
                      unsigned int mtfg_queue_symbol_63; \
                      increment_mtfg_queue_32(); \
                      if (symbol_lengths[mtfg_queue_symbol_63] == 14) { \
                        symbol_is_nonergodic[mtfg_queue_symbol_63] &= 1; \
                        remove_mtfg_queue_symbol_128(); \
                      } \
                      else { \
                        unsigned int mtfg_queue_symbol_127; \
                        increment_mtfg_queue_64(); \
                        if (symbol_lengths[mtfg_queue_symbol_127] == 15) { \
                          symbol_is_nonergodic[mtfg_queue_symbol_127] &= 1; \
                          remove_mtfg_queue_symbol_128(); \
                        } \
                        else { \
                          i4 = mtfg_queue_position - 128; \
                          while (i4) { \
                            *(mtfg_queue_128 + ((mtfg_queue_128_offset + i4) & 0x3F)) \
                                = *(mtfg_queue_128 + ((mtfg_queue_128_offset + i4 - 1) & 0x3F)); \
                            i4--; \
                          } \
                          *(mtfg_queue_128 + mtfg_queue_128_offset) = mtfg_queue_symbol_127; \
                        } \
                      } \
                    } \
                  } \
                  break; \
                } \
                else if (symbol_starts_az[*(mtfg_queue_128 + ((mtfg_queue_position + mtfg_queue_128_offset) & 0x3F))]) \
                  cap_queue_position++; \
              } while (++mtfg_queue_position != 192); \
              if (mtfg_queue_position == 192) { \
                while (symbol_number != *(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F))) { \
                  if (symbol_starts_az[*(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F))]) \
                    cap_queue_position++; \
                  mtfg_queue_position++; \
                } \
                if (prior_is_cap == 0) { \
                  if (in_definition == 0) { \
                    EncodeMtfgType(LEVEL0); \
                  } \
                  else { \
                    EncodeMtfgType(LEVEL1); \
                  } \
                  EncodeMtfgQueuePos(NOT_CAP); \
                } \
                else { \
                  if (in_definition == 0) { \
                    EncodeMtfgType(LEVEL0_CAP); \
                  } \
                  else { \
                    EncodeMtfgType(LEVEL1_CAP); \
                  } \
                  unsigned int saved_qp = mtfg_queue_position; \
                  mtfg_queue_position = cap_queue_position; \
                  EncodeMtfgQueuePos(CAP); \
                  mtfg_queue_position = saved_qp; \
                } \
                if (symbol_lengths[mtfg_queue_symbol_15] <= 12) { \
                  symbol_is_nonergodic[mtfg_queue_symbol_15] &= 1; \
                  remove_mtfg_queue_symbol_192(); \
                } \
                else { \
                  unsigned int mtfg_queue_symbol_31; \
                  increment_mtfg_queue_16(); \
                  if (symbol_lengths[mtfg_queue_symbol_31] == 13) { \
                    symbol_is_nonergodic[mtfg_queue_symbol_31] &= 1; \
                    remove_mtfg_queue_symbol_192(); \
                  } \
                  else { \
                    unsigned int mtfg_queue_symbol_63; \
                    increment_mtfg_queue_32(); \
                    if (symbol_lengths[mtfg_queue_symbol_63] == 14) { \
                      symbol_is_nonergodic[mtfg_queue_symbol_63] &= 1; \
                      remove_mtfg_queue_symbol_192(); \
                    } \
                    else { \
                      unsigned int mtfg_queue_symbol_127; \
                      increment_mtfg_queue_64(); \
                      if (symbol_lengths[mtfg_queue_symbol_127] == 15) { \
                        symbol_is_nonergodic[mtfg_queue_symbol_127] &= 1; \
                        remove_mtfg_queue_symbol_192(); \
                      } \
                      else { \
                        unsigned int mtfg_queue_symbol_191; \
                        increment_mtfg_queue_128(); \
                        if (symbol_lengths[mtfg_queue_symbol_191] == 16) { \
                          symbol_is_nonergodic[mtfg_queue_symbol_191] &= 1; \
                          remove_mtfg_queue_symbol_192(); \
                        } \
                        else { \
                          i4 = mtfg_queue_position - 192; \
                          while (i4) { \
                            *(mtfg_queue_192 + ((mtfg_queue_192_offset + i4) & 0x3F)) \
                                = *(mtfg_queue_192 + ((mtfg_queue_192_offset + i4 - 1) & 0x3F)); \
                            i4--; \
                          } \
                          *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191; \
} } } } } } } } } } } } } \


#define update_code_table(symbol_bits) { \
  num_bins_of_bits[symbol_bits]++; \
  dictionary_bins++; \
  for (table_index = symbol_bits + 1 ; table_index <= max_code_length ; table_index++) \
    first_bin_of_bits[table_index]++; \
}


#define update_code_table_cap(symbol_bits) { \
  num_bins_of_bits_cap[symbol_bits]++; \
  dictionary_bins_cap++; \
  for (table_index = symbol_bits + 1 ; table_index <= max_code_length ; table_index++) \
    first_bin_of_bits_cap[table_index]++; \
}


inline void encode_dictionary_symbol() {
  DictionaryBins = dictionary_bins;
  if (CodeLength > 12) {
    unsigned int max_codes_in_bins, mcib;
    unsigned int reduce_bits = 0;
    max_codes_in_bins = num_bins_of_bits[CodeLength] << (CodeLength - 12);
    mcib = max_codes_in_bins >> 1;
    while (mcib >= num_symbols_of_bits[CodeLength]) {
      reduce_bits++;
      mcib = mcib >> 1;
    }
    if (CodeLength - reduce_bits > 12) {
      BinNum = first_bin_of_bits[CodeLength];
      min_extra_reduce_index = 2 * num_symbols_of_bits[CodeLength] - (max_codes_in_bins >> reduce_bits);
      if (symbol_index >= min_extra_reduce_index) {
        int symbol_bins = 2;
        BinCode = 2 * symbol_index - min_extra_reduce_index;
        unsigned int code_bin = BinCode >> (CodeLength - 12 - reduce_bits);
        BinNum += code_bin;
        BinCode -= code_bin << (CodeLength - 12 - reduce_bits);
        while (BinCode && (symbol_is_nonergodic[symbol_array_of_bits[CodeLength][--symbol_index]] & 2)) {
          if (symbol_index >= min_extra_reduce_index) {
            symbol_bins += 2;
            BinCode -= 2;
          }
          else {
            symbol_bins++;
            BinCode--;
          }
        }
        CodeLength -= reduce_bits;
        EncodeLongDictionarySymbol(symbol_bins);
      }
      else {
        BinCode = symbol_index;
        int symbol_bins = 1;
        while ((BinCode & ((1 << (CodeLength - 12)) - 1))
            && (symbol_is_nonergodic[symbol_array_of_bits[CodeLength][BinCode - 1]] & 2)) {
          symbol_bins++;
          BinCode--;
        }
        CodeLength -= reduce_bits;
        unsigned int code_bin = symbol_index >> (CodeLength - 12);
        BinNum += code_bin;
        BinCode -= code_bin << (CodeLength - 12);
        EncodeLongDictionarySymbol(symbol_bins);
      }
    }
    else {
      int symbol_bins = 1;
      while (symbol_index && (symbol_is_nonergodic[symbol_array_of_bits[CodeLength][symbol_index - 1]] & 2)) {
        symbol_bins++;
        symbol_index--;
      }
      BinNum = first_bin_of_bits[CodeLength] + symbol_index;
      EncodeShortDictionarySymbol(12, symbol_bins);
    }
  }
  else {
    int symbol_bins = 1;
    while (symbol_index && (symbol_is_nonergodic[symbol_array_of_bits[CodeLength][symbol_index - 1]] & 2)) {
      symbol_bins++;
      symbol_index--;
    }
    BinNum = first_bin_of_bits[CodeLength] + (symbol_index << (12 - CodeLength));
    EncodeShortDictionarySymbol(CodeLength, symbol_bins);
  }
}



inline void encode_dictionary_symbol_cap() {
  DictionaryBins = dictionary_bins_cap;
  if (CodeLength > 12) {
    unsigned int reduce_bits = 0;
    unsigned int max_codes_in_bins, mcib;
    max_codes_in_bins = num_bins_of_bits_cap[CodeLength] << (CodeLength - 12);
    mcib = max_codes_in_bins >> 1;
    while (mcib >= num_symbols_of_bits_cap[CodeLength]) {
      reduce_bits++;
      mcib = mcib >> 1;
    }
    if (CodeLength - reduce_bits > 12) {
      BinNum = first_bin_of_bits_cap[CodeLength];
      min_extra_reduce_index = 2 * num_symbols_of_bits_cap[CodeLength] - (max_codes_in_bins >> reduce_bits);
      if (symbol_index >= min_extra_reduce_index) {
        int symbol_bins = 2;
        BinCode = 2 * symbol_index - min_extra_reduce_index;
        unsigned int code_bin = BinCode >> (CodeLength - 12 - reduce_bits);
        BinNum += code_bin;
        BinCode -= code_bin << (CodeLength - 12 - reduce_bits);
        while (BinCode && (symbol_is_nonergodic[symbol_array_of_bits_cap[CodeLength][--symbol_index]] & 2)) {
          if (symbol_index >= min_extra_reduce_index) {
            symbol_bins += 2;
            BinCode -= 2;
          }
          else {
            symbol_bins++;
            BinCode--;
          }
        }
        CodeLength -= reduce_bits;
        EncodeLongDictionarySymbol(symbol_bins);
      }
      else {
        BinCode = symbol_index;
        int symbol_bins = 1;
        while ((BinCode & ((1 << (CodeLength - 12)) - 1))
            && (symbol_is_nonergodic[symbol_array_of_bits_cap[CodeLength][BinCode - 1]] & 2)) {
          symbol_bins++;
          BinCode--;
        }
        CodeLength -= reduce_bits;
        unsigned int code_bin = symbol_index >> (CodeLength - 12);
        BinNum += code_bin;
        BinCode -= code_bin << (CodeLength - 12);
        EncodeLongDictionarySymbol(symbol_bins);
      }
    }
    else {
      int symbol_bins = 1;
      while (symbol_index && (symbol_is_nonergodic[symbol_array_of_bits_cap[CodeLength][symbol_index - 1]] & 2)) {
        symbol_bins++;
        symbol_index--;
      }
      BinNum = first_bin_of_bits_cap[CodeLength] + symbol_index;
      EncodeShortDictionarySymbol(12, symbol_bins);
    }
  }
  else {
    int symbol_bins = 1;
    while (symbol_index && (symbol_is_nonergodic[symbol_array_of_bits_cap[CodeLength][symbol_index - 1]] & 2)) {
      symbol_bins++;
      symbol_index--;
    }
    BinNum = first_bin_of_bits_cap[CodeLength] + (symbol_index << (12 - CodeLength));
    EncodeShortDictionarySymbol(CodeLength, symbol_bins);
  }
}


inline void update_mtf_queue(unsigned int this_symbol, unsigned int symbol_inst, unsigned int this_symbol_count) {
  unsigned int i1, mtf_queue_position;

  mtf_queue_position = MTF_QUEUE_LENGTH;
  if (symbol_inst != this_symbol_count - 1) { // not the last instance
    if (symbol_is_nonergodic[this_symbol]) {
      i1 = mtf_queue_size[this_symbol_count];
      while (i1 != 0) {
        i1--;
        if (mtf_queue[this_symbol_count][i1] == this_symbol) {
          mtf_queue_position = mtf_queue_size[this_symbol_count] - i1 - 1;
          mtf_queue_hit_count[this_symbol_count][mtf_queue_size[this_symbol_count] - i1]++;
          while (i1 < mtf_queue_size[this_symbol_count] - 1) {
            mtf_queue[this_symbol_count][i1] = mtf_queue[this_symbol_count][i1+1];
            i1++;
          }
          mtf_queue[this_symbol_count][i1] = this_symbol;
          return;
        }
      }
    }
    // symbol not in mtf queue, move it back into the queue
    symbol_is_nonergodic[this_symbol] = 1;
    if (mtf_queue_size[this_symbol_count] < MTF_QUEUE_LENGTH)
      mtf_queue[this_symbol_count][mtf_queue_size[this_symbol_count]++] = this_symbol;
    else { // move the queue elements down
      symbol_is_nonergodic[mtf_queue[this_symbol_count][0]] = 0;
      i1 = 0;
      while (i1 < mtf_queue_size[this_symbol_count] - 1) {
        mtf_queue[this_symbol_count][i1] = mtf_queue[this_symbol_count][i1+1];
        i1++;
      }
      mtf_queue[this_symbol_count][i1] = this_symbol;
    }
  }
  else { // last instance
    mtf_queue_done[this_symbol_count]++;
    // default is to return the symbol code and length if no match found
    if (symbol_is_nonergodic[this_symbol]) {
      i1 = mtf_queue_size[this_symbol_count];
      while (i1-- != 0) {
        if (mtf_queue[this_symbol_count][i1] == this_symbol) { // return the mtf queue code and length
          symbol_is_nonergodic[this_symbol] = 0;
          mtf_queue_position = mtf_queue_size[this_symbol_count] - i1 - 1;
          mtf_queue_hit_count[this_symbol_count][(mtf_queue_size[this_symbol_count]--) - i1]++;
          while (i1 < mtf_queue_size[this_symbol_count]) {
            mtf_queue[this_symbol_count][i1] = mtf_queue[this_symbol_count][i1+1];
            i1++;
          }
          return;
        }
      }
    }
  }
}


#define add_dictionary_symbol(symbol, bits) { \
  symbol_index = num_symbols_of_bits[bits]++; \
  symbol_array_of_bits[bits][symbol_index] = symbol; \
  symbol_array_index[symbol] = symbol_index; \
  while ((num_symbols_of_bits[bits] << (32 - bits)) > (num_bins_of_bits[bits] << 20)) { \
    update_code_table(bits); \
  } \
}


#define add_dictionary_symbol_cap(symbol, bits) { \
  symbol_index = num_symbols_of_bits_cap[bits]++; \
  symbol_array_of_bits_cap[bits][symbol_index] = symbol; \
  symbol_array_index_cap[symbol] = symbol_index; \
  while ((num_symbols_of_bits_cap[bits] << (32 - bits)) > (num_bins_of_bits_cap[bits] << 20)) { \
    update_code_table_cap(bits); \
  } \
}


#define remove_dictionary_symbol() { \
  if (cap_encoded && symbol_starts_az[this_symbol]) { \
    symbol_index = symbol_array_index_cap[this_symbol]; \
    symbol_to_move = symbol_array_of_bits_cap[symbol_bits][--num_symbols_of_bits_cap[symbol_bits]]; \
    symbol_array_of_bits_cap[symbol_bits][symbol_index] = symbol_to_move; \
    symbol_array_index_cap[symbol_to_move] = symbol_index; \
  } \
  symbol_index = symbol_array_index[this_symbol]; \
  symbol_to_move = symbol_array_of_bits[symbol_bits][--num_symbols_of_bits[symbol_bits]]; \
  symbol_array_of_bits[symbol_bits][symbol_index] = symbol_to_move; \
  symbol_array_index[symbol_to_move] = symbol_index; \
}


inline void manage_mtf_queue(unsigned int this_symbol, unsigned int symbol_inst, unsigned int this_symbol_count,
    unsigned char in_definition) {
  unsigned int i1, mtf_queue_position;

  mtf_queue_number = (unsigned char)this_symbol_count - 2;
  if (symbol_inst != this_symbol_count - 1) { // not the last instance
    if (symbol_is_nonergodic[this_symbol]) {
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
              unsigned int *end_mtf_queue_ptr = &mtf_queue[this_symbol_count][mtf_queue_size[this_symbol_count] - 1];
              unsigned int *mtf_queue_ptr = end_mtf_queue_ptr - mtf_queue_position + 1;
              do {
                if (symbol_starts_az[*mtf_queue_ptr] == 0)
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
          prior_is_cap = cap_encoded & symbol_ends_cap[this_symbol];
          return;
        }
      }
    }
    // symbol not in mtf queue, return the symbol code and length
    symbol_is_nonergodic[this_symbol] = 1;
    CodeLength = (unsigned int)symbol_lengths[this_symbol];
    if (prior_is_cap == 0) {
      UpFreqMtfQueueNum(NOT_CAP);
      if (in_definition == 0) {
        EncodeDictType(LEVEL0);
      }
      else {
        EncodeDictType(LEVEL1);
      }
      symbol_index = symbol_array_index[this_symbol];
      encode_dictionary_symbol();
    }
    else {
      UpFreqMtfQueueNum(CAP);
      if (in_definition == 0) {
        EncodeDictType(LEVEL0_CAP);
      }
      else {
        EncodeDictType(LEVEL1_CAP);
      }
      symbol_index = symbol_array_index_cap[this_symbol];
      encode_dictionary_symbol_cap();
    }
    // move the symbol back into the mtf queue
    symbol_bits = mtf_queue_overflow_code_length[this_symbol_count];
    if (mtf_queue_size[this_symbol_count] < MTF_QUEUE_LENGTH) {
      mtf_queue[this_symbol_count][mtf_queue_size[this_symbol_count]++] = this_symbol;
      remove_dictionary_symbol();
    }
    else {
      symbol_is_nonergodic[mtf_queue[this_symbol_count][0]] = 0;
      if (cap_encoded) {
        if (symbol_starts_az[this_symbol]) {
          symbol_index = symbol_array_index_cap[this_symbol];
          if (symbol_starts_az[mtf_queue[this_symbol_count][0]]) {
            // give the symbol that is falling out of the queue the index previously assigned to this symbol
            symbol_to_move = mtf_queue[this_symbol_count][0];
            symbol_array_of_bits_cap[symbol_bits][symbol_index] = symbol_to_move;
            symbol_array_index_cap[symbol_to_move] = symbol_index;
          }
          else {
            symbol_to_move = symbol_array_of_bits_cap[symbol_bits][--num_symbols_of_bits_cap[symbol_bits]];
            symbol_array_of_bits_cap[symbol_bits][symbol_index] = symbol_to_move;
            symbol_array_index_cap[symbol_to_move] = symbol_index;
          }
        }
        else if (symbol_starts_az[mtf_queue[this_symbol_count][0]]) {
          symbol_to_move = mtf_queue[this_symbol_count][0];
          add_dictionary_symbol_cap(symbol_to_move, symbol_bits);
        }
      }
      symbol_to_move = mtf_queue[this_symbol_count][0];
      symbol_index = symbol_array_index[this_symbol];
      symbol_array_of_bits[symbol_bits][symbol_index] = symbol_to_move;
      symbol_array_index[symbol_to_move] = symbol_index;
      // move the queue elements down
      while (i1 < mtf_queue_size[this_symbol_count] - 1) {
        mtf_queue[this_symbol_count][i1] = mtf_queue[this_symbol_count][i1+1];
        i1++;
      }
      mtf_queue[this_symbol_count][i1] = this_symbol;
    }
    prior_is_cap = cap_encoded & symbol_ends_cap[this_symbol];
  }
  else { // last instance
    // default is to return the symbol code and length if no match found
    if (symbol_is_nonergodic[this_symbol]) {
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
              unsigned int *end_mtf_queue_ptr = &mtf_queue[this_symbol_count][mtf_queue_size[this_symbol_count] - 1];
              unsigned int *mtf_queue_ptr = end_mtf_queue_ptr - mtf_queue_position + 1;
              do {
                if (symbol_starts_az[*mtf_queue_ptr] == 0)
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
          prior_is_cap = cap_encoded & symbol_ends_cap[this_symbol];
          return;
        }
      }
    }
    // symbol not in mtf queue, return the symbol code and length
    CodeLength = (unsigned int)symbol_lengths[this_symbol];
    if (prior_is_cap == 0) {
      if (in_definition == 0) {
        EncodeDictType(LEVEL0);
      }
      else {
        EncodeDictType(LEVEL1);
      }
      symbol_index = symbol_array_index[this_symbol];
      encode_dictionary_symbol();
    }
    else {
      if (in_definition == 0) {
        EncodeDictType(LEVEL0_CAP);
      }
      else {
        EncodeDictType(LEVEL1_CAP);
      }
      symbol_index = symbol_array_index_cap[this_symbol];
      encode_dictionary_symbol_cap();
    }
    symbol_bits = mtf_queue_overflow_code_length[this_symbol_count];
    remove_dictionary_symbol();
    prior_is_cap = cap_encoded & symbol_ends_cap[this_symbol];
  }
}


inline void manage_mtf_symbol(unsigned int this_symbol, unsigned int symbol_inst, unsigned int this_symbol_count,
    unsigned char in_definition) {
  CodeLength = (unsigned int)symbol_lengths[this_symbol];
  if (prior_is_cap == 0) {
    if (in_definition == 0) {
      EncodeDictType(LEVEL0);
    }
    else {
      EncodeDictType(LEVEL1);
    }
    symbol_index = symbol_array_index[this_symbol];
    encode_dictionary_symbol();
  }
  else {
    if (in_definition == 0) {
      EncodeDictType(LEVEL0_CAP);
    }
    else {
      EncodeDictType(LEVEL1_CAP);
    }
    symbol_index = symbol_array_index_cap[this_symbol];
    encode_dictionary_symbol_cap();
  }
  prior_is_cap = cap_encoded & symbol_ends_cap[this_symbol];
  if (symbol_inst == this_symbol_count - 1) { // last instance
    symbol_bits = mtf_queue_overflow_code_length[this_symbol_count];
    remove_dictionary_symbol();
  }
}


inline unsigned int count_symbols(unsigned int this_symbol) {
  unsigned int symbol_number;
  unsigned int *symbol_string_ptr, *end_symbol_string_ptr;
  unsigned int string_symbols;

  if (this_symbol < START_MY_SYMBOLS)
    return(1);
  symbol_number = this_symbol - START_MY_SYMBOLS;
  symbol_string_ptr = define_symbol_start_ptr[symbol_number];
  end_symbol_string_ptr = define_symbol_start_ptr[symbol_number+1] - 1;

  string_symbols = 0;
  while (symbol_string_ptr != end_symbol_string_ptr) {
    if ((symbol_count[*symbol_string_ptr] == 1) && (*symbol_string_ptr >= START_MY_SYMBOLS))
      string_symbols += count_symbols(*symbol_string_ptr);
    else
      string_symbols++;
    symbol_string_ptr++;
  }
  return(string_symbols);
}


void count_embedded_definition_symbols(unsigned int define_symbol) {
  unsigned int *define_string_ptr, *this_define_symbol_start_ptr, *define_string_end_ptr;
  unsigned int define_symbol_instances, symbol_number, symbol_inst;
  unsigned int i1;
  unsigned int this_symbol, this_symbol_count;

  if ((symbol_count[define_symbol] == 1) && (define_symbol >= START_MY_SYMBOLS)) {
    // count the symbols in the string instead of creating a single instance symbol (artifacts of TreeCompress)
    symbol_number = define_symbol - START_MY_SYMBOLS;
    define_string_ptr = define_symbol_start_ptr[symbol_number];
    define_string_end_ptr = define_symbol_start_ptr[symbol_number+1] - 1;
    while (define_string_ptr != define_string_end_ptr) {
      this_symbol = *define_string_ptr++;
      symbol_inst = symbol_inst_found[this_symbol]++;
      define_symbol_instances = symbol_count[this_symbol];
      if (symbol_inst == 0)
        count_embedded_definition_symbols(this_symbol);
      else if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE)
        update_mtf_queue(this_symbol,symbol_inst,define_symbol_instances);
      else {
        CodeLength = (unsigned int)symbol_lengths[this_symbol];
        if (CodeLength >= 11) {
          if (symbol_is_nonergodic[this_symbol] & 2) {
            manage_mtfg_queue1(this_symbol);
            mtfg_hits[this_symbol]++;
            mtfg_hits2[this_symbol]++;
          }
          else {
            add_symbol_to_mtfg_queue(this_symbol);
          }
        }
      }
    }
    return;
  }

  // write the code for the symbol code length
  define_symbol_instances = symbol_count[define_symbol];
  if (define_symbol_instances != 1) { // calculate the new code
    if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE)
      symbol_code_length = mtf_queue_overflow_code_length[define_symbol_instances];
    else
      symbol_code_length = (unsigned int)symbol_lengths[define_symbol];
  }

  // count the symbols in the definition
  if (define_symbol >= START_MY_SYMBOLS) {
    symbol_number = define_symbol - START_MY_SYMBOLS;
    this_define_symbol_start_ptr = define_symbol_start_ptr[symbol_number];
    define_string_ptr = this_define_symbol_start_ptr;
    define_string_end_ptr = define_symbol_start_ptr[symbol_number+1] - 1;
    while (define_string_ptr != define_string_end_ptr) {
      this_symbol = *define_string_ptr++;
      symbol_inst = symbol_inst_found[this_symbol]++;
      this_symbol_count = symbol_count[this_symbol];
      if (symbol_inst == 0)
        count_embedded_definition_symbols(this_symbol);
      else if (this_symbol_count <= MAX_INSTANCES_FOR_MTF_QUEUE)
        update_mtf_queue(this_symbol,symbol_inst,this_symbol_count);
      else {
        CodeLength = (unsigned int)symbol_lengths[this_symbol];
        if (CodeLength >= 11) {
          if (symbol_is_nonergodic[this_symbol] & 2) {
            manage_mtfg_queue1(this_symbol);
            mtfg_hits[this_symbol]++;
            mtfg_hits2[this_symbol]++;
          }
          else {
            add_symbol_to_mtfg_queue(this_symbol);
          }
        }
      }
    }
  }

  if (define_symbol_instances != 1) { // assign symbol code
    if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE) { // Handle initial mtf instance
      symbol_is_nonergodic[define_symbol] = 1;
      mtf_queue_started[define_symbol_instances]++;
      if (mtf_queue_started[define_symbol_instances] - mtf_queue_done[define_symbol_instances]
          > mtf_queue_peak[define_symbol_instances])
        mtf_queue_peak[define_symbol_instances]++;
      if (mtf_queue_size[define_symbol_instances] < MTF_QUEUE_LENGTH)
        mtf_queue[define_symbol_instances][mtf_queue_size[define_symbol_instances]++] = define_symbol;
      else {
        symbol_is_nonergodic[mtf_queue[define_symbol_instances][i1]] = 0;
        for (i1=0 ; i1<63 ; i1++)
          mtf_queue[define_symbol_instances][i1] = mtf_queue[define_symbol_instances][i1+1];
        mtf_queue[define_symbol_instances][63] = define_symbol;
      }
    }
    else {
      CodeLength = (unsigned int)symbol_lengths[define_symbol];
      if (CodeLength >= 11) {
        add_symbol_to_mtfg_queue(define_symbol);
      }
    }
  }
  num_define_symbols_written++;
}


void embed_define(unsigned int define_symbol, unsigned char in_definition) {
  unsigned int *define_string_ptr, *this_define_symbol_start_ptr, *define_string_end_ptr;
  unsigned int define_symbol_instances, symbols_in_definition, symbol_number, symbol_inst;
  unsigned int i1, new_symbol_code_length, this_symbol, this_symbol_count;
  unsigned char char_before_define_is_cap;

  if ((symbol_count[define_symbol] == 1) && (define_symbol >= START_MY_SYMBOLS)) {
    // write the symbol string instead of creating a single instance symbol (artifacts of TreeCompress)
    symbol_number = define_symbol - START_MY_SYMBOLS;
    define_string_ptr = define_symbol_start_ptr[symbol_number];
    define_string_end_ptr = define_symbol_start_ptr[symbol_number+1] - 1;
    while (define_string_ptr != define_string_end_ptr) {
      this_symbol = *define_string_ptr++;
      symbol_inst = symbol_inst_found[this_symbol]++;
      define_symbol_instances = symbol_count[this_symbol];
      if (symbol_inst == 0)
        embed_define(this_symbol, in_definition);
      else if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE) {
        if (use_mtf) {
          manage_mtf_queue(this_symbol,symbol_inst,define_symbol_instances,in_definition);
        }
        else {
          manage_mtf_symbol(this_symbol,symbol_inst,define_symbol_instances,in_definition);
        }
      }
      else {
        if (symbol_is_nonergodic[this_symbol] & 2) {
          manage_mtfg_queue(this_symbol,in_definition);
          prior_is_cap = cap_encoded & symbol_ends_cap[this_symbol];
        }
        else {
          CodeLength = (unsigned int)symbol_lengths[this_symbol];
          if (prior_is_cap == 0) {
            if (in_definition == 0) {
              EncodeDictType(LEVEL0);
            }
            else {
              EncodeDictType(LEVEL1);
            }
            prior_is_cap = cap_encoded & symbol_ends_cap[this_symbol];
            symbol_index = symbol_array_index[this_symbol];
            encode_dictionary_symbol();
          }
          else {
            if (in_definition == 0) {
              EncodeDictType(LEVEL0_CAP);
            }
            else {
              EncodeDictType(LEVEL1_CAP);
            }
            prior_is_cap = symbol_ends_cap[this_symbol];
            symbol_index = symbol_array_index_cap[this_symbol];
            encode_dictionary_symbol_cap();
          }
          if (symbol_is_nonergodic[this_symbol]) {
            add_symbol_to_mtfg_queue(this_symbol);
          }
        }
      }
    }
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

  define_symbol_instances = symbol_count[define_symbol];
  if (define_symbol_instances != 1) { // get the code length for the new symbol
    if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE)
      new_symbol_code_length = mtf_queue_overflow_code_length[define_symbol_instances];
    else
      new_symbol_code_length = (unsigned int)symbol_lengths[define_symbol];
  }

  // get the code for the new symbol frequency and length
  if (define_symbol < START_MY_SYMBOLS) {
    SIDSymbol = 0;
    if (define_symbol_instances == 1)
      Symbol = MAX_INSTANCES_FOR_MTF_QUEUE - 1;
    else if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE)
      Symbol = define_symbol_instances - 2;
    else
      Symbol = MAX_INSTANCES_FOR_MTF_QUEUE + max_regular_code_length - new_symbol_code_length;
    if (prior_is_cap == 0) {
      EncodeSID(NOT_CAP);
      EncodeINST(NOT_CAP);
    }
    else {
      EncodeSID(CAP);
      EncodeINST(CAP);
    }
    if ((define_symbol_instances > MAX_INSTANCES_FOR_MTF_QUEUE) && (use_mtf || (max_code_length >= 12))
        && (new_symbol_code_length >= 11) && (define_symbol_instances != 1)) {
      EncodeERG(symbol_is_nonergodic[define_symbol]);
    }
    BaseSymbol = define_symbol;
    EncodeBaseSymbol(base_bits);
    char_before_define_is_cap = prior_is_cap;
    prior_is_cap = cap_encoded & symbol_ends_cap[define_symbol];
  }
  else {
    symbol_number = define_symbol - START_MY_SYMBOLS;
    this_define_symbol_start_ptr = define_symbol_start_ptr[symbol_number];
    define_string_ptr = this_define_symbol_start_ptr;
    define_string_end_ptr = define_symbol_start_ptr[symbol_number+1] - 1;

    // count the symbols in the definition
    symbols_in_definition = 0;
    while (define_string_ptr != define_string_end_ptr) {
      if ((symbol_count[*define_string_ptr] != 1) || (*define_string_ptr < START_MY_SYMBOLS))
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
      int extra_symbols = symbols_in_definition - 16;
      int temp2 = extra_symbols;
      int data_bits = 1;
      while (temp2 >= (1 << data_bits))
        temp2 -= (1 << data_bits++);
      temp2 = data_bits;
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
      Symbol = MAX_INSTANCES_FOR_MTF_QUEUE + max_regular_code_length - new_symbol_code_length;
    if (prior_is_cap == 0) {
      EncodeINST(NOT_CAP);
    }
    else {
      EncodeINST(CAP);
    }

    if ((define_symbol_instances > MAX_INSTANCES_FOR_MTF_QUEUE) && (use_mtf || (max_code_length >= 12))
        && (new_symbol_code_length >= 11) && (define_symbol_instances != 1)) {
      EncodeERG(symbol_is_nonergodic[define_symbol]);
    }

    char_before_define_is_cap = prior_is_cap;

    // write the symbol string
    define_string_ptr = this_define_symbol_start_ptr;
    while (define_string_ptr != define_string_end_ptr) {
      this_symbol = *define_string_ptr++;
      symbol_inst = symbol_inst_found[this_symbol]++;
      this_symbol_count = symbol_count[this_symbol];
      if (symbol_inst == 0)
        embed_define(this_symbol, 1);
      else if (this_symbol_count <= MAX_INSTANCES_FOR_MTF_QUEUE) {
        if (use_mtf) {
          manage_mtf_queue(this_symbol,symbol_inst,this_symbol_count,1);
        }
        else {
          manage_mtf_symbol(this_symbol,symbol_inst,this_symbol_count,1);
        }
      }
      else {
        CodeLength = (unsigned int)symbol_lengths[this_symbol];
        if (symbol_is_nonergodic[this_symbol] & 2) {
          manage_mtfg_queue(this_symbol,1);
          prior_is_cap = cap_encoded & symbol_ends_cap[this_symbol];
        }
        else {
          if (prior_is_cap == 0) {
            EncodeDictType(LEVEL1);
            prior_is_cap = cap_encoded & symbol_ends_cap[this_symbol];
            symbol_index = symbol_array_index[this_symbol];
            encode_dictionary_symbol();
          }
          else {
            EncodeDictType(LEVEL1_CAP);
            prior_is_cap = symbol_ends_cap[this_symbol];
            symbol_index = symbol_array_index_cap[this_symbol];
            encode_dictionary_symbol_cap();
          }
          if (symbol_is_nonergodic[this_symbol]) {
            add_symbol_to_mtfg_queue(this_symbol);
          }
        }
      }
    }
  }

  if (define_symbol_instances != 1) { // assign symbol code
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
        symbol_is_nonergodic[define_symbol] = 1;
        if (mtf_queue_size[define_symbol_instances] < MTF_QUEUE_LENGTH) {
          mtf_queue[define_symbol_instances][mtf_queue_size[define_symbol_instances]++] = define_symbol;
        }
        else {
          if (cap_encoded && symbol_starts_az[mtf_queue[define_symbol_instances][0]]) {
            symbol_to_move = mtf_queue[define_symbol_instances][0];
            symbol_is_nonergodic[symbol_to_move] = 0;
            add_dictionary_symbol_cap(symbol_to_move, new_symbol_code_length);
          }
          symbol_to_move = mtf_queue[define_symbol_instances][0];
          add_dictionary_symbol(symbol_to_move, new_symbol_code_length);
          for (i1=0 ; i1<63 ; i1++)
            mtf_queue[define_symbol_instances][i1] = mtf_queue[define_symbol_instances][i1+1];
          mtf_queue[define_symbol_instances][63] = define_symbol;
        }
      }
      else {
        // Handle initial mtf symbol instance
        add_dictionary_symbol(define_symbol, new_symbol_code_length);
        if (cap_encoded && symbol_starts_az[define_symbol]) {
          add_dictionary_symbol_cap(define_symbol, new_symbol_code_length);
        }
      }
    }
    else {
      if (symbol_is_nonergodic[define_symbol]) {
        add_symbol_to_mtfg_queue(define_symbol);
      }
      add_dictionary_symbol(define_symbol, new_symbol_code_length);
      if (cap_encoded && symbol_starts_az[define_symbol]) {
        add_dictionary_symbol_cap(define_symbol, new_symbol_code_length);
      }
    }
  }
  num_define_symbols_written++;
}


int main(int argc, char* argv[]) {
  FILE *fd_in, *fd_out;

  unsigned char this_char, arg_num, verbose;
  unsigned char *string_ptr, *string_end_ptr;
  unsigned int i1, i2, in_size, num_symbols, num_symbols_defined, num_definitions_to_code, num_chars_to_read;
  unsigned int UTF8_value, max_UTF8_value, this_symbol, this_symbol_count, symbol_inst, end_symbols, next_symbol;
  unsigned int min_sorted_symbols, sorted_symbols_save, num_sorted_symbols, remaining_symbols_to_code, remaining_code_space;
  unsigned int string_ptr_index, mtf_queue_hits, mtfg_symbols_reduced;
  unsigned int *define_string_ptr, *define_string_end_ptr, *end_symbol_ptr, *define_symbol_start_ptr_array_ptr;
  unsigned int *sorted_symbols_ptr, *end_sorted_symbols_ptr, *min_sorted_symbols_ptr, *max_sorted_symbols_ptr;
  unsigned int *min_one_instance_sorted_symbols_ptr, *next_sorted_symbol_ptr, *temp_sorted_symbols_ptr;
  double d_remaining_symbols_to_code, log2_inv;
  unsigned long long int start_time;


  start_time = clock();

  for (i1 = 2 ; i1 <= MAX_INSTANCES_FOR_MTF_QUEUE ; i1++) {
    mtf_queue_started[i1] = 0;
    mtf_queue_done[i1] = 0;
    mtf_queue_peak[i1] = 0;
    mtf_queue_size[i1] = 0;
    for (i2 = 0 ; i2 < MTF_QUEUE_LENGTH ; i2++)
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
  if (*argv[1] ==  '-') {
    if (*(argv[1]+1) != 'v') {
      fprintf(stderr,"ERROR - Invalid '-' format.  Only -v allowed\n");
      exit(0);
    }
    arg_num = 2;
    verbose = 1;
  }
  if((fd_in=fopen(argv[arg_num],"rb")) == NULL) {
    fprintf(stderr,"fopen error - '%s'\n",argv[arg_num]);
    exit(0);
  }
  arg_num++;

  // read the file into local memory
  fseek(fd_in, 0, SEEK_END);
  in_size = ftell(fd_in);
  rewind(fd_in);

  in_char_ptr = in_data;
  end_char_ptr = in_data + in_size;
  fread(in_data,1,READ_SIZE+3,fd_in);
  num_chars_to_read = in_size - READ_SIZE - 3;

  cap_encoded = *in_char_ptr++; 
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
  }

  rewind(fd_in);
  fread(in_data,1,READ_SIZE+3,fd_in);
  num_chars_to_read = in_size - READ_SIZE - 3;
  in_char_ptr = in_data + 1;
  end_char_ptr = in_data + in_size;
  num_symbols = 0;
  num_symbols_defined = 0;
  symbol_ptr = symbol;
  if (UTF8_compliant) {
    while (in_char_ptr < end_char_ptr) {
      if (symbol_ptr - symbol == MAX_FILE_SYMBOLS) {
        fprintf(stderr,"ERROR - symbol limit of %u symbols exceeded\n",MAX_FILE_SYMBOLS);
        exit(0);
      }
      if (in_char_ptr - in_data >= READ_SIZE) {
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
        this_symbol = START_MY_SYMBOLS;
        this_symbol += 0x10000 * (unsigned int)*in_char_ptr++;
        this_symbol += 0x100 * (unsigned int)*in_char_ptr++;
        this_symbol += (unsigned int)*in_char_ptr++;
        *symbol_ptr++ = this_symbol;
      }
      else if (this_char == DEFINE_SYMBOL_CHAR) {
        if (first_define_ptr == 0)
          first_define_ptr = symbol_ptr;
        in_char_ptr += 3;
        *symbol_ptr++ = (DEFINE_SYMBOL_CHAR<<24)+num_symbols_defined;
        define_symbol_start_ptr[num_symbols_defined++] = symbol_ptr;
      }
      else if (this_char < START_UTF8_2BYTE_SYMBOLS) {
        *symbol_ptr++ = (unsigned int)this_char;
      }
      else {
        if (this_char >= 0xF8) { // not a UTF-8 character
          fprintf(stderr,"ERROR - non UTF-8 character %x\n",this_char);
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
        else if (this_char >= 0xC0) // 2 byte UTF-8 character
          UTF8_value = 0x40 * (this_char & 0x1F);
        UTF8_value += *in_char_ptr++ & 0x3F;
        *symbol_ptr++ = UTF8_value;
      }
    }
    base_bits = 0;
    while (max_UTF8_value) {
      max_UTF8_value >>= 1;
      base_bits++;
    }
  }
  else {
    while (in_char_ptr < end_char_ptr) {
      if (symbol_ptr - symbol == MAX_FILE_SYMBOLS) {
        fprintf(stderr,"ERROR - symbol limit of %u symbols exceeded\n",MAX_FILE_SYMBOLS);
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
      if (this_char < INSERT_SYMBOL_CHAR) {
        *symbol_ptr++ = (unsigned int)this_char;
      }
      else if (*in_char_ptr == DEFINE_SYMBOL_CHAR) {
        *symbol_ptr++ = (unsigned int)this_char;
        in_char_ptr++;
      }
      else if (this_char == INSERT_SYMBOL_CHAR) {
        this_symbol = START_MY_SYMBOLS;
        this_symbol += 0x10000 * (unsigned int)*in_char_ptr++;
        this_symbol += 0x100 * (unsigned int)*in_char_ptr++;
        this_symbol += (unsigned int)*in_char_ptr++;
        *symbol_ptr++ = this_symbol;
      }
      else {
        if (first_define_ptr == 0)
          first_define_ptr = symbol_ptr;
        in_char_ptr += 3;
        *symbol_ptr++ = (DEFINE_SYMBOL_CHAR<<24)+num_symbols_defined;
        define_symbol_start_ptr[num_symbols_defined++] = symbol_ptr;
      }
    }
    base_bits = 8;
  }
  fclose(fd_in);
  fprintf(stderr,"cap encoded %u, UTF8 compliant %u\n",cap_encoded,UTF8_compliant);

  if (first_define_ptr == 0)
    first_define_ptr = symbol_ptr;
  *symbol_ptr = UNIQUE_CHAR;
  define_symbol_start_ptr[num_symbols_defined] = symbol_ptr+1;

  end_symbol_ptr = symbol_ptr;
  num_symbols = end_symbol_ptr - symbol;
  end_symbols = START_MY_SYMBOLS + num_symbols_defined;

  fprintf(stderr,"Read %u symbols including %u definition symbols\n",num_symbols,num_symbols_defined);

  // count the number of instances of each symbol
  for (i1 = 0 ; i1 < end_symbols ; i1++)
    symbol_count[i1] = 0;
  symbol_ptr = symbol;
  while (symbol_ptr != end_symbol_ptr) {
    if (*symbol_ptr >= DEFINE_SYMBOL_CHAR<<24)
      symbol_ptr++;
    else
      symbol_count[*symbol_ptr++]++;
  }

  if (verbose)
    for (i1 = 0 ; i1 < end_symbols ; i1++)
      orig_symbol_count[i1] = symbol_count[i1];

  if (cap_encoded) {
    i1 = 0;
    do {
      symbol_starts_az[i1] = 0;
      symbol_ends_cap[i1] = 0;
    } while (++i1 < 0x61);
    do {
      symbol_starts_az[i1] = 1;
      symbol_ends_cap[i1] = 0;
    } while (++i1 < 0x7B);
    do {
      symbol_starts_az[i1] = 0;
      symbol_ends_cap[i1] = 0;
    } while (++i1 < START_MY_SYMBOLS);
    symbol_ends_cap[CAP_CHAR] = 1;
    do {
      next_symbol = *define_symbol_start_ptr[i1-START_MY_SYMBOLS];
      while (next_symbol >= i1)
        next_symbol = *define_symbol_start_ptr[next_symbol-START_MY_SYMBOLS];
      symbol_starts_az[i1] = symbol_starts_az[next_symbol];
      next_symbol = *(define_symbol_start_ptr[i1-START_MY_SYMBOLS+1]-2);
      while (next_symbol >= i1)
        next_symbol = *(define_symbol_start_ptr[next_symbol-START_MY_SYMBOLS+1]-2);
      symbol_ends_cap[i1] = symbol_ends_cap[next_symbol];
    } while (++i1 < end_symbols);
  }

  sorted_symbols_ptr = sorted_symbols;
  for (i1=0 ; i1<end_symbols ; i1++)
    if (symbol_count[i1] != 0)
      *sorted_symbols_ptr++ = i1;
  end_sorted_symbols_ptr = sorted_symbols_ptr;
  min_sorted_symbols_ptr = sorted_symbols_ptr;

  // move single instance symbols to the end of the sorted symbols array
  sorted_symbols_ptr = sorted_symbols;
  while (sorted_symbols_ptr < min_sorted_symbols_ptr) {
    if (symbol_count[*sorted_symbols_ptr] == 1) { // move this symbol to the top of the moved to end 1 instance symbols
      sorted_symbols_save = *sorted_symbols_ptr;
      *sorted_symbols_ptr = *--min_sorted_symbols_ptr;
      *min_sorted_symbols_ptr = sorted_symbols_save;
    }
    else
      sorted_symbols_ptr++;
  }
  min_one_instance_sorted_symbols_ptr = min_sorted_symbols_ptr;

  // sort symbols with 800 or fewer instances by putting them at the end of the sorted symbols array
  for (i1=2 ; i1<801 ; i1++) {
    sorted_symbols_ptr = sorted_symbols;
    while (sorted_symbols_ptr < min_sorted_symbols_ptr) {
      if (symbol_count[*sorted_symbols_ptr] == i1) {
        sorted_symbols_save = *sorted_symbols_ptr;
        *sorted_symbols_ptr = *--min_sorted_symbols_ptr;
        *min_sorted_symbols_ptr = sorted_symbols_save;
      }
      else
        sorted_symbols_ptr++;
    }
  }

  // sort the remaining symbols by moving the most frequent symbols to the top of the sorted symbols array
  min_sorted_symbols = min_sorted_symbols_ptr - sorted_symbols;
  for (i1=0 ; i1<min_sorted_symbols ; i1++) {
    unsigned int max_symbol_count = 0;
    sorted_symbols_ptr = &sorted_symbols[i1];
    while (sorted_symbols_ptr < min_sorted_symbols_ptr) {
      if (symbol_count[*sorted_symbols_ptr] > max_symbol_count) {
        max_symbol_count = symbol_count[*sorted_symbols_ptr];
        max_sorted_symbols_ptr = sorted_symbols_ptr;
      }
      sorted_symbols_ptr++;
    }
    if (max_symbol_count > 0) {
      sorted_symbols_save = sorted_symbols[i1];
      sorted_symbols[i1] = *max_sorted_symbols_ptr;
      *max_sorted_symbols_ptr = sorted_symbols_save;
    }
  }
  num_sorted_symbols = end_sorted_symbols_ptr - sorted_symbols;
  num_symbols_to_code = num_symbols - (end_sorted_symbols_ptr - sorted_symbols);
  num_definitions_to_code = min_one_instance_sorted_symbols_ptr - sorted_symbols;
  num_define_symbols_written = 0;

  log2_inv = 1.0/log(2.0);

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

  remaining_code_space += remaining_code_space >> 5;
  remaining_symbols_to_code += remaining_symbols_to_code >> 5;
  max_regular_code_length = 1;
  num_regular_definitions = 0;

  for (i1=0 ; i1<num_definitions_to_code ; i1++) {
    symbol_inst = symbol_count[sorted_symbols[i1]] - 1;
    d_remaining_symbols_to_code = (double)remaining_symbols_to_code;
    symbol_code_length = (unsigned int)(log2_inv * log(1.4 * (d_remaining_symbols_to_code / (double)symbol_inst)
             * ((double)(1 << 30) / (double)(remaining_code_space - 0x20))));
    if (symbol_code_length < 2) // limit so files with less than 2 bit symbols (ideally) work
      symbol_code_length = 2;
    if (symbol_inst >= MAX_INSTANCES_FOR_MTF_QUEUE) {
      num_regular_definitions++;
      if (symbol_code_length > 24)
        symbol_code_length = 24;
      if (symbol_code_length > max_regular_code_length)
        max_regular_code_length = symbol_code_length;
    }
    symbol_lengths[sorted_symbols[i1]] = (unsigned char)symbol_code_length;
    remaining_code_space -= (1 << (30 - symbol_code_length));
    remaining_symbols_to_code -= symbol_inst;
  }

  for (i1=0 ; i1<end_symbols ; i1++) {
    symbol_inst_found[i1] = 0;
    mtfg_hits[i1] = 0;
    mtfg_hits2[i1] = 0;
    symbol_is_nonergodic[i1] = 0;
  }

  symbol_ptr = symbol;
  while (symbol_ptr < first_define_ptr) {
    if (((symbol_ptr - symbol) & 0x3FFFFF) == 0)
      fprintf(stderr,"Parsed %u of %u level 0 symbols\r",symbol_ptr-symbol,first_define_ptr-symbol);
    this_symbol = *symbol_ptr++;
    this_symbol_count = symbol_count[this_symbol];
    symbol_inst = symbol_inst_found[this_symbol]++;
    if (symbol_inst == 0)
      count_embedded_definition_symbols(this_symbol);
    else if (this_symbol_count <= MAX_INSTANCES_FOR_MTF_QUEUE)
      update_mtf_queue(this_symbol,symbol_inst,this_symbol_count);
    else {
      CodeLength = (unsigned int)symbol_lengths[this_symbol];
      if (CodeLength >= 11) {
        if (symbol_is_nonergodic[this_symbol] & 2) {
          manage_mtfg_queue1(this_symbol);
          mtfg_hits[this_symbol]++;
          mtfg_hits2[this_symbol]++;
        }
        else {
          add_symbol_to_mtfg_queue(this_symbol);
        }
      }
    }
  }
  fprintf(stderr,"Parsed %u level 0 symbols              \r",first_define_ptr-symbol);

  use_mtf = 0;
  if ((mtf_queue_peak[2] >= 0x80) && (log(num_symbols) + (double)(4 * mtf_queue_started[2]) / (double)mtf_queue_peak[2] >= 22.0))
  {
    use_mtf = 1;
    mtfg_symbols_reduced = 0;
    for (i1 = 0 ; i1 < end_symbols ; i1++) {
      if ((symbol_count[i1] > 20) && (symbol_lengths[i1] >= 11) && (mtfg_hits2[i1] > ((symbol_count[i1] * 9) >> 4))) {
        symbol_is_nonergodic[i1] = 1;
        if (symbol_count[i1] - mtfg_hits[i1] <= 20) {
          mtfg_symbols_reduced += symbol_count[i1] - 21;
          symbol_count[i1] = 21;
        }
        else {
          mtfg_symbols_reduced += mtfg_hits[i1];
          symbol_count[i1] -= mtfg_hits[i1];
        }
      }
    }
  }

  // sort symbols with 800 or fewer instances by putting them at the end of the sorted symbols array
  next_sorted_symbol_ptr = sorted_symbols + num_regular_definitions - 1;
  for (i1=21 ; i1<801 ; i1++) {
    while ((next_sorted_symbol_ptr > sorted_symbols) && (symbol_count[*next_sorted_symbol_ptr] == i1))
      next_sorted_symbol_ptr--;
    sorted_symbols_ptr = next_sorted_symbol_ptr - 1;
    while (sorted_symbols_ptr >= sorted_symbols) {
      if (symbol_count[*sorted_symbols_ptr] == i1) {
        sorted_symbols_save = *sorted_symbols_ptr;
        *sorted_symbols_ptr-- = *next_sorted_symbol_ptr;
        *next_sorted_symbol_ptr-- = sorted_symbols_save;
      }
      else
        sorted_symbols_ptr--;
    }
  }

  for (i1 = 1 ; i1 < num_regular_definitions ; i1++) {
    unsigned int temp_symbol = sorted_symbols[i1];
    unsigned int temp_symbol_count = symbol_count[temp_symbol];
    if (temp_symbol_count > symbol_count[sorted_symbols[i1-1]]) {
      i2 = i1 - 1;
      sorted_symbols[i1] = sorted_symbols[i2];
      while (i2 && (temp_symbol_count > symbol_count[sorted_symbols[i2-1]])) {
        sorted_symbols[i2] = sorted_symbols[i2-1];
        i2--;
      }
      sorted_symbols[i2] = temp_symbol;
    }
  }

  for (i1=0 ; i1<end_symbols ; i1++)
    symbol_inst_found[i1] = 0;

  mtfg_queue_8_offset = 0;
  mtfg_queue_16_offset = 0;
  mtfg_queue_32_offset = 0;
  mtfg_queue_64_offset = 0;
  mtfg_queue_128_offset = 0;
  mtfg_queue_192_offset = 0;
  for (i1 = 0 ; i1 < 8 ; i1++)
    mtfg_queue_0[i1] = 0xFFFFFFFF;
  for (i1 = 0 ; i1 < 8 ; i1++)
    mtfg_queue_8[i1] = 0xFFFFFFFF;
  for (i1 = 0 ; i1 < 16 ; i1++)
    mtfg_queue_16[i1] = 0xFFFFFFFF;
  for (i1 = 0 ; i1 < 32 ; i1++)
    mtfg_queue_32[i1] = 0xFFFFFFFF;
  for (i1 = 0 ; i1 < 64 ; i1++)
    mtfg_queue_64[i1] = 0xFFFFFFFF;
  for (i1 = 0 ; i1 < 64 ; i1++)
    mtfg_queue_128[i1] = 0xFFFFFFFF;
  for (i1 = 0 ; i1 < 64 ; i1++)
    mtfg_queue_192[i1] = 0xFFFFFFFF;

  for (i1=2 ; i1 <= MAX_INSTANCES_FOR_MTF_QUEUE ; i1++) { /* PUT i1=2 OUTSIDE OF LOOP */
    mtf_queue_hits = 0;
    for (i2=1 ; i2 <= MTF_QUEUE_LENGTH ; i2++)
      mtf_queue_hits += mtf_queue_hit_count[i1][i2];
    
    if (mtf_queue_peak[i1] > MTF_QUEUE_LENGTH) {
      if (i1 != 2) {
        if (use_mtf)
          mtf_queue_overflow_code_length[i1] = (unsigned int)(0.6 + log2_inv * log((double)num_symbols_to_code / (double)(i1-1)
              * (double)i1 / (double)(i1+1)
              * (double)((mtf_queue_peak[i1]-MTF_QUEUE_LENGTH)*(i1-1)) / (double)(mtf_queue_started[i1]*(i1-1)-mtf_queue_hits)
              * 0.5 * (1.0 + (double)((mtf_queue_peak[i1]-MTF_QUEUE_LENGTH)*(i1-1))
                / (double)(mtf_queue_started[i1]*(i1-1)-mtf_queue_hits))));
        else
          mtf_queue_overflow_code_length[i1] = (unsigned int)(0.6 + log2_inv * log((double)num_symbols_to_code / (double)(i1-1)
              * (double)i1 / (double)(i1+1) * (double)(mtf_queue_peak[i1]*(i1-1)) / (double)(mtf_queue_started[i1]*(i1-1))));
        if (mtf_queue_overflow_code_length[i1] > mtf_queue_overflow_code_length[i1-1])
          mtf_queue_overflow_code_length[i1] = mtf_queue_overflow_code_length[i1-1];
        else if (mtf_queue_overflow_code_length[i1] < mtf_queue_overflow_code_length[i1-1] - 1)
          mtf_queue_overflow_code_length[i1] = mtf_queue_overflow_code_length[i1-1] - 1;
      }
      else {
        if (use_mtf) {
          mtf_queue_overflow_code_length[2] = (unsigned int)(0.3 + log2_inv * log((double)num_symbols_to_code
              * (double)(mtf_queue_peak[2]-MTF_QUEUE_LENGTH) / (double)(mtf_queue_started[2]-mtf_queue_hits)
              * 0.5 * (1.0 + (double)(mtf_queue_peak[2]-MTF_QUEUE_LENGTH) / (double)(mtf_queue_started[2]-mtf_queue_hits))));
          if (mtf_queue_overflow_code_length[2] > 25)
            mtf_queue_overflow_code_length[2] = 25;
        }
        else {
          mtf_queue_overflow_code_length[2] = (unsigned int)(0.3 + log2_inv * log((double)num_symbols_to_code
              * (double)mtf_queue_peak[2] / (double)mtf_queue_started[2]));
          if (mtf_queue_overflow_code_length[2] > 25)
            mtf_queue_overflow_code_length[2] = 25;
        }
      }
    }
    else if (i1 == 2) {
      if (mtf_queue_started[2]) {
        mtf_queue_overflow_code_length[2] = (unsigned int)(0.3 + log2_inv * log((double)num_symbols_to_code
            * (double)mtf_queue_peak[2] / (double)mtf_queue_started[2]));
        if (mtf_queue_overflow_code_length[2] > 25)
          mtf_queue_overflow_code_length[2] = 25;
      }
      else
        mtf_queue_overflow_code_length[2] = 25;
    }
    else {
      if (mtf_queue_started[i1] && (use_mtf == 0)) {
        mtf_queue_overflow_code_length[i1] = (unsigned int)(0.6 + log2_inv * log((double)num_symbols_to_code / (double)(i1-1)
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

  for (i1 = 0 ; i1 < 8 ; i1++)
    mtfg_queue_0[i1] = 0xFFFFFFFF;
  for (i1 = 0 ; i1 < 8 ; i1++)
    mtfg_queue_8[i1] = 0xFFFFFFFF;
  for (i1 = 0 ; i1 < 16 ; i1++)
    mtfg_queue_16[i1] = 0xFFFFFFFF;
  for (i1 = 0 ; i1 < 32 ; i1++)
    mtfg_queue_32[i1] = 0xFFFFFFFF;
  for (i1 = 0 ; i1 < 64 ; i1++)
    mtfg_queue_64[i1] = 0xFFFFFFFF;
  for (i1 = 0 ; i1 < 64 ; i1++)
    mtfg_queue_128[i1] = 0xFFFFFFFF;
  for (i1 = 0 ; i1 < 64 ; i1++)
    mtfg_queue_192[i1] = 0xFFFFFFFF;

  if (use_mtf) {
    mtf_queue_miss_code_space = 0;
    mtf_overflow_symbols_to_code = 0;
    for (i1 = 2 ; i1 <= MAX_INSTANCES_FOR_MTF_QUEUE ; i1++) {
      if (mtf_queue_peak[i1] > MTF_QUEUE_LENGTH)
        mtf_queue_miss_code_space += (1 << (30 - mtf_queue_overflow_code_length[i1])) * (mtf_queue_peak[i1] - MTF_QUEUE_LENGTH);
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

  // Now repeat the conversion, knowing how many symbols are needed for 2 - 20 instance symbols that fall out of mtf queues
  num_define_symbols_written = 0;
  remaining_symbols_to_code = num_symbols_to_code - mtf_overflow_symbols_to_code - num_symbols_defined - mtfg_symbols_reduced;
  remaining_code_space = (1 << 30);
  remaining_code_space -= 1 << (30 - max_code_length); // reserve space for EOF
  remaining_code_space -= 0x02000000; // reserve code space for define symbols so they don't get too long
  remaining_code_space -= mtf_queue_miss_code_space; // reserve code space for symbols that overflow mtf queues
  remaining_code_space += remaining_code_space >> 5;
  remaining_symbols_to_code += remaining_symbols_to_code >> 5;
  max_regular_code_length = 1;
  if (verbose)
    printf("Coding %u symbols\n",num_symbols_to_code);
  for (i1=0 ; i1<num_definitions_to_code ; i1++) {
    symbol_inst = symbol_count[sorted_symbols[i1]];
    if (symbol_inst <= MAX_INSTANCES_FOR_MTF_QUEUE) {
      symbol_code_length = mtf_queue_overflow_code_length[symbol_inst];
      symbol_lengths[sorted_symbols[i1]] = (unsigned char)symbol_code_length;
    }
    else {
      num_regular_definitions--;
      d_remaining_symbols_to_code = (double)remaining_symbols_to_code;
      symbol_code_length = (unsigned int)(log2_inv * log(1.4 * (d_remaining_symbols_to_code / (double)(--symbol_inst))
               * ((double)(1 << 30)/(double)(remaining_code_space - 0x20))));
      if (symbol_code_length < 2) // limit so files with less than 2 bit symbols (ideally) work
        symbol_code_length = 2;
      if (symbol_code_length > 24)
        symbol_code_length = 24;
      while (remaining_code_space - (1 << (30 - symbol_code_length))
          < num_regular_definitions * (0x40000000 >> (max_code_length - 1)))
        symbol_code_length++;
      if (symbol_code_length > max_regular_code_length)
        max_regular_code_length = symbol_code_length;
      if (symbol_code_length < 11)
        symbol_is_nonergodic[sorted_symbols[i1]] = 0;
      symbol_lengths[sorted_symbols[i1]] = (unsigned char)symbol_code_length;
      remaining_code_space -= (1 << (30 - symbol_code_length));
      remaining_symbols_to_code -= symbol_inst;
      symbol_is_nonergodic[sorted_symbols[i1]] &= 1;
    }
    if (verbose) {
      if ((symbol_code_length >= 11) && (orig_symbol_count[sorted_symbols[i1]] > 20))
        printf("%u: #%u %u L%u D%u: \"",i1,orig_symbol_count[sorted_symbols[i1]],symbol_count[sorted_symbols[i1]],
            symbol_code_length,symbol_is_nonergodic[sorted_symbols[i1]]);
      else
        printf("%u: #%u L%u: \"",i1,orig_symbol_count[sorted_symbols[i1]],symbol_code_length);
      print_string(sorted_symbols[i1]);
      printf("\"\n");
    }
  }

  i1 = max_code_length;
  num_symbols_of_bits[i1] = 1;
  symbol_array_of_bits[i1][0] = 0x9FFFFF;
  symbol_is_nonergodic[0x9FFFFF] = 0;
  if (i1 >= 12) {
    num_bins_of_bits[i1] = 1;
    dictionary_bins = 1;
  }
  else {
    num_bins_of_bits[i1] = 1 << (12 - max_code_length);
    dictionary_bins = 1 << (12 - max_code_length);
  }
  first_bin_of_bits[i1--] = 0;
  while (i1 != 0) {
    num_symbols_of_bits[i1] = 0;
    num_bins_of_bits[i1] = 0;
    first_bin_of_bits[i1--] = 0;
  }

  if (cap_encoded) {
    i1 = max_code_length;
    num_symbols_of_bits_cap[i1] = 1;
    symbol_array_of_bits_cap[i1][0] = 0x9FFFFF;
    if (max_code_length >= 12) {
      num_bins_of_bits_cap[i1] = 1;
      dictionary_bins_cap = 1;
    }
    else {
      num_bins_of_bits_cap[i1] = 1 << (12 - max_code_length);
      dictionary_bins_cap = 1 << (12 - max_code_length);
    }
    first_bin_of_bits_cap[i1--] = 0;
    while (i1 != 0) {
      num_symbols_of_bits_cap[i1] = 0;
      num_bins_of_bits_cap[i1] = 0;
      first_bin_of_bits_cap[i1--] = 0;
    }
  }

  if((fd_out = fopen(argv[arg_num],"wb")) == NULL) {
    printf("fopen error - %s\n",argv[arg_num]);
    exit(0);
  }

  for (i1=0 ; i1<end_symbols ; i1++)
    symbol_inst_found[i1] = 0;
  symbol_ptr = symbol;
  prior_is_cap = 0;

  InitEncoder(fd_out);
  OutData[OutCharNum++] = (cap_encoded << 7) | (UTF8_compliant << 6) | (use_mtf << 5) | base_bits;
  OutData[OutCharNum++] = mtf_queue_overflow_code_length[2] - 1;
  OutData[OutCharNum++] = ((mtf_queue_overflow_code_length[3] != mtf_queue_overflow_code_length[2]) << 7)
      | ((mtf_queue_overflow_code_length[4] != mtf_queue_overflow_code_length[3]) << 6)
      | (max_regular_code_length - 1);
  for (i1 = 0 ; i1 <= 7 ; i1++)
    this_char = (this_char << 1) | (mtf_queue_overflow_code_length[i1 + 5] != mtf_queue_overflow_code_length[i1 + 4]);
  OutData[OutCharNum++] = this_char;
  for (i1 = 0 ; i1 <= 7 ; i1++)
    this_char = (this_char << 1) | (mtf_queue_overflow_code_length[i1 + 13] != mtf_queue_overflow_code_length[i1 + 12]);
  OutData[OutCharNum++] = this_char;

  while (symbol_ptr < first_define_ptr) {
    if (((symbol_ptr-symbol)&0x1FFFFF) == 0)
      fprintf(stderr,"Encoded %u of %u level 1 symbols\r",symbol_ptr-symbol,first_define_ptr-symbol);
    this_symbol = *symbol_ptr++;
    this_symbol_count = symbol_count[this_symbol];
    symbol_inst = symbol_inst_found[this_symbol]++;
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
    }
    else {
      if (symbol_is_nonergodic[this_symbol] & 2) {
        manage_mtfg_queue(this_symbol,0);
        prior_is_cap = cap_encoded & symbol_ends_cap[this_symbol];
      }
      else {
        CodeLength = (unsigned int)symbol_lengths[this_symbol];
        if (prior_is_cap == 0) {
          EncodeDictType(LEVEL0);
          prior_is_cap = cap_encoded & symbol_ends_cap[this_symbol];
          symbol_index = symbol_array_index[this_symbol];
          encode_dictionary_symbol();
        }
        else {
          EncodeDictType(LEVEL0_CAP);
          prior_is_cap = symbol_ends_cap[this_symbol];
          symbol_index = symbol_array_index_cap[this_symbol];
          encode_dictionary_symbol_cap();
        }
        if (symbol_is_nonergodic[this_symbol])
          add_symbol_to_mtfg_queue(this_symbol);
      }
    }
  }

  // send EOF and flush output
  CodeLength = max_code_length;
  if (prior_is_cap == 0) {
    EncodeDictType(LEVEL0);
    BinNum = first_bin_of_bits[max_code_length];
    DictionaryBins = dictionary_bins;
    if (max_code_length > 12) {
      BinCode = 0;
      EncodeLongDictionarySymbol(1);
    }
    else {
      EncodeShortDictionarySymbol(max_code_length, 1);
    }
  }
  else {
    EncodeDictType(LEVEL0_CAP);
    DictionaryBins = dictionary_bins_cap;
    BinNum = first_bin_of_bits_cap[max_code_length];
    if (max_code_length > 12) {
      BinCode = 0;
      EncodeLongDictionarySymbol(1);
    }
    else {
      EncodeShortDictionarySymbol(max_code_length, 1);
    }
  }
  FinishEncoder();
  fprintf(stderr,"Encoded %u level 1 symbols             \n",symbol_ptr-symbol,first_define_ptr-symbol);
  fprintf(stderr,"Compressed file size: %u bytes, dictionary size: %u symbols\n",ftell(fd_out),num_define_symbols_written);
  fclose(fd_out);
  fprintf(stderr,"elapsed time = %f seconds.\n", 0.001*(float)(clock()-start_time));
}