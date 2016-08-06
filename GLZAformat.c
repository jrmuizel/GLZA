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

// GLZAformat.c
//   Adds 0xFF after all 0xFE and 0xFF bytes to support compressions insert and define symbols.
//   Replaces 'A' - 'Z' with 'C' followed by the corresponding lower case letter or
//     'B' followed by a series of lower case letters when text detected.
//   For non-text files, checks order 0 entropy of standard coding vs. delta coding for 1, 2 and 4
//   byte values (entire file).  Delta transforms data when appropriate.
//
// Usage:
//   GLZAformat [-c#] [-d#] [-l#] <infilename> <outfilename>, where
//       -c0 disables capital encoding
//       -c1 forces text processing and capital encoding
//       -d0 disables delta encoding
//       -l0 disables capital lock encoding


#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include "GLZA.h"

const U32 CHARS_TO_WRITE = 0x40000;
U8 * in_char;
U8 out_char_buffer[0x40010];


#define update_capital_statistics() { \
  if ((this_char >= 'A') && (this_char <= 'Z')) { \
    num_AZ++; \
    prev_char = *(in_char_ptr - 2); \
    next_char = *in_char_ptr; \
    if (((next_char >= 'a') && (next_char <= 'z')) || ((next_char >= 'A') && (next_char <= 'Z'))) \
      num_az_post_AZ++; \
    if (((prev_char >= 'a') && (prev_char <= 'z')) || ((prev_char >= 'A') && (prev_char <= 'Z'))) \
      num_az_pre_AZ++; \
  } \
}


int main(int argc, char* argv[])
{
  FILE *fd_in, *fd_out;
  U8 arg_num, this_char, prev_char, next_char, user_cap_encoded, user_cap_lock_encoded, user_delta_encoded;
  U8 *in_char_ptr, *end_char_ptr, *out_char_ptr;
  U32 num_in_char, num_out_char, i;
  U32 num_AZ, num_az_pre_AZ, num_az_post_AZ;
  U32 symbol_counts0[0x100], symbol_counts1[0x100], symbol_counts2[0x100], symbol_counts3[0x100], symbol_counts4[0x100];
  clock_t start_time;
  double order_0_entropy0, order_0_entropy1, order_0_entropy2, order_0_entropy3, order_0_entropy4;

  // format byte: B0: cap encoded, B3:B1 = stride (0 - 4), B5:B4 = log2 delta length (0 - 2), B6: little endian


  start_time = clock();

  user_cap_encoded = 0;
  user_cap_lock_encoded = 0;
  user_delta_encoded = 0;

  arg_num = 1;
  while (*argv[arg_num] ==  '-') {
    if (*(argv[arg_num]+1) == 'c') {
      user_cap_encoded = 1 + *(argv[arg_num++] + 2) - '0';
      if ((user_cap_encoded < 1) || (user_cap_encoded > 2)) {
        fprintf(stderr,"ERROR: -c value must be 0 or 1\n");
        exit(0);
      }
    }
    if (*(argv[arg_num]+1) == 'l') {
      user_cap_lock_encoded = 1 + *(argv[arg_num++] + 2) - '0';
      if ((user_cap_lock_encoded < 1) || (user_cap_lock_encoded > 2)) {
        fprintf(stderr,"ERROR: -l value must be 0 or 1\n");
        exit(0);
      }
    }
    else if (*(argv[arg_num]+1) == 'd') {
      user_delta_encoded = 1 + *(argv[arg_num++] + 2) - '0';
      if ((user_delta_encoded < 1) || (user_delta_encoded > 2)) {
        fprintf(stderr,"ERROR: -d value must be 0 or 1\n");
        exit(0);
      }
    }
    else {
      fprintf(stderr,"ERROR - Invalid '-' format.  Only -c<value> and -d<value> allowed\n");
      exit(0);
    }
  }

  if (argc != arg_num + 2) {
    fprintf(stderr,"ERROR - Command format is \"GLZAformat [-c#] [-d#] [-l0] <infile> <outfile>\"\n");
    exit(0);
  }
  if ((fd_in = fopen(argv[arg_num],"rb"))==NULL) {
    fprintf(stderr,"ERROR - Unable to open input file '%s'\n",argv[arg_num]);
    exit(0);
  }
  if ((fd_out = fopen(argv[++arg_num],"wb"))==NULL) {
    fprintf(stderr,"ERROR - Unable to open output file '%s'\n",argv[arg_num]);
    exit(0);
  }

  fseek(fd_in, 0, SEEK_END);
  num_in_char = ftell(fd_in);
  rewind(fd_in);
  fprintf(stderr,"Reading %u byte file\n",num_in_char);

  in_char = (uint8_t *)malloc(num_in_char + 1);
  in_char[num_in_char] = 0;
  num_in_char = fread(in_char, 1, num_in_char, fd_in);
  fclose(fd_in);

  end_char_ptr = in_char + num_in_char;
  num_AZ = 0;
  num_az_pre_AZ = 0;
  num_az_post_AZ = 0;

  for (i = 0 ; i < 0x100 ; i++) {
    symbol_counts0[i] = 0;
    symbol_counts1[i] = 0;
    symbol_counts2[i] = 0;
    symbol_counts3[i] = 0;
    symbol_counts4[i] = 0;
  }

  if (num_in_char > 4) {
    in_char_ptr = in_char;
    this_char = *in_char_ptr++;
    symbol_counts0[this_char]++;
    symbol_counts1[this_char]++;
    symbol_counts2[this_char]++;
    symbol_counts3[this_char]++;
    symbol_counts4[this_char]++;
    if ((this_char >= 'A') && (this_char <= 'Z')) {
      num_AZ++;
      next_char = *in_char_ptr;
      if (((next_char >= 'a') && (next_char <= 'z')) || ((next_char >= 'A') && (next_char <= 'Z')))
        num_az_post_AZ++;
    }

    this_char = *in_char_ptr++;
    symbol_counts0[this_char]++;
    symbol_counts1[(unsigned char)(this_char - *(in_char_ptr-2))]++;
    symbol_counts2[this_char]++;
    symbol_counts3[this_char]++;
    symbol_counts4[this_char]++;
    update_capital_statistics();

    this_char = *in_char_ptr++;
    symbol_counts0[this_char]++;
    symbol_counts1[(unsigned char)(this_char - *(in_char_ptr-2))]++;
    symbol_counts2[(unsigned char)(this_char - *(in_char_ptr-3))]++;
    symbol_counts3[this_char]++;
    symbol_counts4[this_char]++;
    update_capital_statistics();

    this_char = *in_char_ptr++;
    symbol_counts0[this_char]++;
    symbol_counts1[(unsigned char)(this_char - *(in_char_ptr-2))]++;
    symbol_counts2[(unsigned char)(this_char - *(in_char_ptr-3))]++;
    symbol_counts3[(unsigned char)(this_char - *(in_char_ptr-4))]++;
    symbol_counts4[this_char]++;
    update_capital_statistics();

    while (in_char_ptr != end_char_ptr) {
      this_char = *in_char_ptr++;
      symbol_counts0[this_char]++;
      symbol_counts1[(unsigned char)(this_char - *(in_char_ptr-2))]++;
      symbol_counts2[(unsigned char)(this_char - *(in_char_ptr-3))]++;
      symbol_counts3[(unsigned char)(this_char - *(in_char_ptr-4))]++;
      symbol_counts4[(unsigned char)(this_char - *(in_char_ptr-5))]++;
      update_capital_statistics();
    }
  }

  out_char_ptr = out_char_buffer;
  num_out_char = 0;

  if (((num_AZ && (4 * num_az_post_AZ > num_AZ) && (num_az_post_AZ > num_az_pre_AZ)
      && (symbol_counts0[0x20] > num_in_char / 50)) && (user_cap_encoded != 1)) || (user_cap_encoded == 2)) {
    fprintf(stderr,"Converting textual data\n");
    fputc(1,fd_out);
    in_char_ptr = in_char;
    while (in_char_ptr != end_char_ptr) {
      if ((*in_char_ptr >= 'A') && (*in_char_ptr <= 'Z')) {
        if (((*(in_char_ptr + 1) >= 'A') && (*(in_char_ptr + 1) <= 'Z') && (user_cap_lock_encoded != 1))
            && ((*(in_char_ptr + 2) < 'a') || (*(in_char_ptr + 2) > 'z'))) {
          *out_char_ptr++ = 'B';
          *out_char_ptr++ = *in_char_ptr++ + ('a' - 'A');
          *out_char_ptr++ = *in_char_ptr++ + ('a' - 'A');
          while ((*in_char_ptr >= 'A') && (*in_char_ptr <= 'Z')) {
            *out_char_ptr++ = *in_char_ptr++ + ('a' - 'A');
            if (out_char_ptr - out_char_buffer >= CHARS_TO_WRITE) {
              fwrite(out_char_buffer, 1, out_char_ptr - out_char_buffer, fd_out);
              num_out_char += out_char_ptr - out_char_buffer;
              out_char_ptr = out_char_buffer;
              fflush(fd_out);
            }
          }
          if ((*in_char_ptr >= 'a') && (*in_char_ptr <= 'z'))
            *out_char_ptr++ = 'C';
        }
        else {
          *out_char_ptr++ = 'C';
          *out_char_ptr++ = *in_char_ptr++ + ('a' - 'A');
        }
      }
      else if (*in_char_ptr >= 0xFE) {
        *out_char_ptr++ = *in_char_ptr++;
        *out_char_ptr++ = 0xFF;
      }
      else if (*in_char_ptr == 0xA) {
        in_char_ptr++;
        *out_char_ptr++ = 0xA;
        *out_char_ptr++ = ' ';
      }
      else
        *out_char_ptr++ = *in_char_ptr++;

      if (out_char_ptr - out_char_buffer >= CHARS_TO_WRITE) {
        fwrite(out_char_buffer, 1, out_char_ptr - out_char_buffer, fd_out);
        num_out_char += out_char_ptr - out_char_buffer;
        out_char_ptr = out_char_buffer;
        fflush(fd_out);
      }
    }
  }
  else if ((user_delta_encoded != 1) && (num_in_char > 4)) {
    order_0_entropy0 = log2((double)num_in_char) * (double)num_in_char;
    order_0_entropy1 = order_0_entropy0;
    order_0_entropy2 = order_0_entropy0;
    order_0_entropy3 = order_0_entropy0;
    order_0_entropy4 = order_0_entropy0;
    for (i = 0 ; i < 0x100 ; i++) {
      if (symbol_counts0[i]) {
        double d_count = (double)symbol_counts0[i];
        order_0_entropy0 -= d_count * log2(d_count);
      }
      if (symbol_counts1[i]) {
        double d_count = (double)symbol_counts1[i];
        order_0_entropy1 -= d_count * log2(d_count);
      }
      if (symbol_counts2[i]) {
        double d_count = (double)symbol_counts2[i];
        order_0_entropy2 -= d_count * log2(d_count);
      }
      if (symbol_counts3[i]) {
        double d_count = (double)symbol_counts3[i];
        order_0_entropy3 -= d_count * log2(d_count);
      }
      if (symbol_counts4[i]) {
        double d_count = (double)symbol_counts4[i];
        order_0_entropy4 -= d_count * log2(d_count);
      }
    }
    double min_entropy = order_0_entropy0 * 0.95;
    U8 stride = 0;
    if (order_0_entropy1 < min_entropy) {
      min_entropy = order_0_entropy1;
      stride = 1;
    }
    if (order_0_entropy2 < min_entropy) {
      min_entropy = order_0_entropy2;
      stride = 2;
    }
    if (order_0_entropy3 < min_entropy) {
      min_entropy = order_0_entropy3;
      stride = 3;
    }
    if (order_0_entropy4 < min_entropy) {
      min_entropy = order_0_entropy4;
      stride = 4;
    }

    if (stride)
      fprintf(stderr,"Applying %u byte delta transformation\n",(unsigned int)stride);
    else
      fprintf(stderr,"Converting data\n");

    if (stride == 0)
      fputc(0, fd_out);
    else if (stride == 1) {
      fputc(2, fd_out);
      in_char_ptr = end_char_ptr - 1;
      while (--in_char_ptr >= in_char)
        *(in_char_ptr + 1) -= *in_char_ptr;
    }
    else if (stride == 2) {
      for (i = 0 ; i < 0x100 ; i++) {
        symbol_counts1[i] = 0;
        symbol_counts2[i] = 0;
      }
      in_char_ptr = in_char;
      symbol_counts1[*in_char_ptr++]++;
      symbol_counts2[*in_char_ptr++]++;
      while (in_char_ptr < end_char_ptr - 2) {
        symbol_counts1[(unsigned char)(*in_char_ptr - *(in_char_ptr - 2))]++;
        in_char_ptr++;
        symbol_counts2[(unsigned char)(*in_char_ptr - *(in_char_ptr - 2))]++;
        in_char_ptr++;
      }
      order_0_entropy1 = log2((double)(num_in_char >> 1)) * (double)(num_in_char >> 1);
      order_0_entropy2 = order_0_entropy1;
      for (i = 0 ; i < 0x100 ; i++) {
        if (symbol_counts1[i]) {
          double d_count = (double)symbol_counts1[i];
          order_0_entropy1 -= d_count * log2(d_count);
        }
        if (symbol_counts2[i]) {
          double d_count = (double)symbol_counts2[i];
          order_0_entropy2 -= d_count * log2(d_count);
        }
      }

      for (i = 0 ; i < 0x100 ; i++)
        symbol_counts0[i] = 0;
      in_char_ptr = in_char;
      symbol_counts0[*in_char_ptr++]++;
      symbol_counts0[*in_char_ptr++]++;
      if (order_0_entropy1 < order_0_entropy2) {
        // big endian
        U32 prior_value = (*(in_char_ptr - 2) << 8) + *(in_char_ptr - 1);
        while (in_char_ptr <= end_char_ptr - 2) {
          U32 value = (*in_char_ptr << 8) + *(in_char_ptr + 1);
          U32 delta_value = value - prior_value + 0x8080;
          symbol_counts0[delta_value & 0xFF]++;
          symbol_counts0[(delta_value >> 8) & 0xFF]++;
          prior_value = value;
          in_char_ptr += 2;
        }
        if (in_char_ptr != end_char_ptr)
          symbol_counts0[(U8)((*in_char_ptr) - *(in_char_ptr-4))]++;
        order_0_entropy1 = log2((double)num_in_char) * (double)num_in_char;
        for (i = 0 ; i < 0x100 ; i++) {
          if (symbol_counts0[i]) {
            double d_count = (double)symbol_counts0[i];
            order_0_entropy1 -= d_count * log2(d_count);
          }
        }
        if (order_0_entropy1 < min_entropy) {
          fprintf(stderr,"Big endian\n");
          fputc(0x14, fd_out);
          in_char_ptr = in_char + ((end_char_ptr - in_char - 4) & ~1);
          U32 value = (*(in_char_ptr + 2) << 8) + *(in_char_ptr + 3);
          while (in_char_ptr >= in_char) {
            U32 prior_value = (*in_char_ptr << 8) + *(in_char_ptr + 1);
            U32 delta_value = value - prior_value + 0x80;
            *(in_char_ptr + 2) = (delta_value >> 8) & 0xFF;
            *(in_char_ptr + 3) = delta_value & 0xFF;
            value = prior_value;
            in_char_ptr -= 2;
          }
        }
        else {
          fprintf(stderr,"No carry\n");
          fputc(0x4, fd_out);
          in_char_ptr = end_char_ptr - 2;
          while (--in_char_ptr >= in_char)
            *(in_char_ptr + 2) -= *in_char_ptr;
        }
      }
      else {
        // little endian
        U32 prior_value = (*(in_char_ptr - 1) << 8) + *(in_char_ptr - 2);
        while (in_char_ptr <= end_char_ptr - 2) {
          U32 value = (*(in_char_ptr + 1) << 8) + *in_char_ptr;
          U32 delta_value = value - prior_value + 0x8080;
          symbol_counts0[delta_value & 0xFF]++;
          symbol_counts0[(delta_value >> 8) & 0xFF]++;
          prior_value = value;
          in_char_ptr += 2;
        }
        if (in_char_ptr != end_char_ptr)
          symbol_counts0[(U8)((*in_char_ptr) - *(in_char_ptr-4))]++;
        order_0_entropy1 = log2((double)num_in_char) * (double)num_in_char;
        for (i = 0 ; i < 0x100 ; i++) {
          if (symbol_counts0[i]) {
            double d_count = (double)symbol_counts0[i];
            order_0_entropy1 -= d_count * log2(d_count);
          }
        }
        if (order_0_entropy1 < min_entropy) {
          fprintf(stderr,"Little endian\n");
          fputc(0x54, fd_out);
          in_char_ptr = in_char + ((end_char_ptr - in_char - 4) & ~1);
          U32 value = (*(in_char_ptr + 3) << 8) + *(in_char_ptr + 2);
          while (in_char_ptr >= in_char) {
            U32 prior_value = (*(in_char_ptr + 1) << 8) + *in_char_ptr;
            U32 delta_value = value - prior_value + 0x80;
            *(in_char_ptr + 2) = delta_value & 0xFF;
            *(in_char_ptr + 3) = (delta_value >> 8) & 0xFF;
            value = prior_value;
            in_char_ptr -= 2;
          }
        }
        else {
          fprintf(stderr,"No carry\n");
          fputc(0x4, fd_out);
          in_char_ptr = end_char_ptr - 2;
          while (--in_char_ptr >= in_char)
            *(in_char_ptr + 2) -= *in_char_ptr;
        }
      }
    }
    else if (stride == 3) {
      fputc(6, fd_out);
      in_char_ptr = end_char_ptr - 3;
      while (--in_char_ptr >= in_char)
        *(in_char_ptr + 3) -= *in_char_ptr;
    }
    else { // stride 4
      for (i = 0 ; i < 0x100 ; i++) {
        symbol_counts1[i] = 0;
        symbol_counts2[i] = 0;
        symbol_counts3[i] = 0;
        symbol_counts4[i] = 0;
      }
      symbol_counts1[*in_char_ptr++]++;
      symbol_counts2[*in_char_ptr++]++;
      symbol_counts3[*in_char_ptr++]++;
      symbol_counts4[*in_char_ptr++]++;
      in_char_ptr = in_char;
      while (in_char_ptr <= end_char_ptr - 4) {
        symbol_counts1[(unsigned char)(*in_char_ptr - *(in_char_ptr - 4))]++;
        in_char_ptr++;
        symbol_counts2[(unsigned char)(*in_char_ptr - *(in_char_ptr - 4))]++;
        in_char_ptr++;
        symbol_counts3[(unsigned char)(*in_char_ptr - *(in_char_ptr - 4))]++;
        in_char_ptr++;
        symbol_counts4[(unsigned char)(*in_char_ptr - *(in_char_ptr - 4))]++;
        in_char_ptr++;
      }
      order_0_entropy1 = log2((double)(num_in_char >> 2)) * (double)(num_in_char >> 2);
      order_0_entropy2 = order_0_entropy1;
      order_0_entropy3 = order_0_entropy1;
      order_0_entropy4 = order_0_entropy1;
      for (i = 0 ; i < 0x100 ; i++) {
        if (symbol_counts1[i]) {
          double d_count = (double)symbol_counts1[i];
          order_0_entropy1 -= d_count * log2(d_count);
        }
        if (symbol_counts2[i]) {
          double d_count = (double)symbol_counts2[i];
          order_0_entropy2 -= d_count * log2(d_count);
        }
        if (symbol_counts3[i]) {
          double d_count = (double)symbol_counts3[i];
          order_0_entropy3 -= d_count * log2(d_count);
        }
        if (symbol_counts4[i]) {
          double d_count = (double)symbol_counts4[i];
          order_0_entropy4 -= d_count * log2(d_count);
        }
      }
      U16 j;
      double best_entropy[4];
      double average_entropy = 0.25 * (order_0_entropy1 + order_0_entropy2 + order_0_entropy3 + order_0_entropy4);
      U8 best_entropy_position[4];
      if (order_0_entropy2 > order_0_entropy1) {
        best_entropy[0] = order_0_entropy1;
        best_entropy[1] = order_0_entropy2;
        best_entropy_position[0] = 0;
        best_entropy_position[1] = 1;
      }
      else {
        best_entropy[0] = order_0_entropy2;
        best_entropy[1] = order_0_entropy1;
        best_entropy_position[0] = 1;
        best_entropy_position[1] = 0;
      }
      i = 2;
      do {
        if (order_0_entropy3 > best_entropy[i-1])
          break;
        best_entropy[i] = best_entropy[i-1];
        best_entropy_position[i] = best_entropy_position[i-1];
      } while (--i);
      best_entropy[i] = order_0_entropy3;
      best_entropy_position[i] = 2;
      i = 3;
      do {
        if (order_0_entropy4 > best_entropy[i-1])
          break;
        best_entropy[i] = best_entropy[i-1];
        best_entropy_position[i] = best_entropy_position[i-1];
      } while (--i);
      best_entropy[i] = order_0_entropy4;
      best_entropy_position[i] = 3;

      if (best_entropy[3] > 1.05 * best_entropy[0]) {
        in_char_ptr = in_char;
        while (in_char_ptr < in_char + 4) {
          symbol_counts0[*in_char_ptr]++;
          in_char_ptr++;
        }
        if ((best_entropy[1] < average_entropy)
            && ((best_entropy_position[0] - best_entropy_position[1] == 2)
              || (best_entropy_position[1] - best_entropy_position[0] == 2))) {
          for (j = 0 ; j < 0x100 ; j++)
            symbol_counts0[j] = 0;
          if (best_entropy[0] + best_entropy[2] < best_entropy[1] + best_entropy[3]) {
            // big endian
            while (in_char_ptr <= end_char_ptr - 2) {
              U32 delta_value = (*in_char_ptr << 8) + *(in_char_ptr + 1)
                  - ((*(in_char_ptr - 4) << 8) + *(in_char_ptr - 3)) + 0x8080;
              symbol_counts0[delta_value & 0xFF]++;
              symbol_counts0[(delta_value >> 8) & 0xFF]++;
              in_char_ptr += 2;
            }
            if (in_char_ptr != end_char_ptr)
              symbol_counts0[(U8)((*in_char_ptr) - *(in_char_ptr-4))]++;
            order_0_entropy1 = log2((double)num_in_char) * (double)num_in_char;
            for (i = 0 ; i < 0x100 ; i++) {
              if (symbol_counts0[i]) {
                double d_count = (double)symbol_counts0[i];
                order_0_entropy1 -= d_count * log2(d_count);
              }
            }
            if (order_0_entropy1 < min_entropy) {
              fprintf(stderr,"Two channel big endian\n");
              fputc(0x18, fd_out);
              in_char_ptr = in_char + ((end_char_ptr - in_char - 6) & ~1);
              while (in_char_ptr >= in_char) {
                U32 delta_value = (*(in_char_ptr + 4) << 8) + *(in_char_ptr + 5)
                    - ((*in_char_ptr << 8) + *(in_char_ptr + 1)) + 0x80;
                *(in_char_ptr + 4) = (delta_value >> 8) & 0xFF;
                *(in_char_ptr + 5) = delta_value & 0xFF;
                in_char_ptr -= 2;
              }
            }
            else {
              fprintf(stderr,"No carry\n");
              fputc(0x8, fd_out);
              in_char_ptr = end_char_ptr - 4;
              while (--in_char_ptr >= in_char)
                *(in_char_ptr + 4) -= *in_char_ptr;
            }
          }
          else {
            // little endian
            while (in_char_ptr <= end_char_ptr - 2) {
              U32 delta_value = (*(in_char_ptr + 1) << 8) + *in_char_ptr
                  - ((*(in_char_ptr - 3) << 8) + *(in_char_ptr - 4)) + 0x8080;
              symbol_counts0[delta_value & 0xFF]++;
              symbol_counts0[(delta_value >> 8) & 0xFF]++;
              in_char_ptr += 2;
            }
            if (in_char_ptr != end_char_ptr)
              symbol_counts0[(U8)((*in_char_ptr) - *(in_char_ptr-4))]++;
            order_0_entropy1 = log2((double)num_in_char) * (double)num_in_char;
            for (i = 0 ; i < 0x100 ; i++) {
              if (symbol_counts0[i]) {
                double d_count = (double)symbol_counts0[i];
                order_0_entropy1 -= d_count * log2(d_count);
              }
            }
            if (order_0_entropy1 < min_entropy) {
              fprintf(stderr,"Two channel little endian\n");
              fputc(0x98, fd_out);
              in_char_ptr = in_char + ((end_char_ptr - in_char - 6) & ~1);
              while (in_char_ptr >= in_char) {
                U32 delta_value = (*(in_char_ptr + 5) << 8) + *(in_char_ptr + 4)
                    - ((*(in_char_ptr + 1) << 8) + *in_char_ptr) + 0x80;
                *(in_char_ptr + 4) = delta_value & 0xFF;
                *(in_char_ptr + 5) = (delta_value >> 8) & 0xFF;
                in_char_ptr -= 2;
              }
            }
            else {
              fprintf(stderr,"No carry\n");
              fputc(0x8, fd_out);
              in_char_ptr = end_char_ptr - 4;
              while (--in_char_ptr >= in_char)
                *(in_char_ptr + 4) -= *in_char_ptr;
            }
          }
        }
        else {
          for (j = 0 ; j < 0x100 ; j++) {
            symbol_counts0[j] = 0;
            symbol_counts1[j] = 0;
          }
          U32 prior_value0 = (*(in_char_ptr - 4) << 24) + (*(in_char_ptr - 3) << 16)
              + (*(in_char_ptr - 2) << 8) + *(in_char_ptr - 1);
          U32 prior_value1 = (*(in_char_ptr - 1) << 24) + (*(in_char_ptr - 2) << 16)
              + (*(in_char_ptr - 3) << 8) + *(in_char_ptr - 4);
          while (in_char_ptr <= end_char_ptr - 4) {
            U32 value = (*in_char_ptr << 24) + (*(in_char_ptr + 1) << 16)
                + (*(in_char_ptr + 2) << 8) + *(in_char_ptr + 3);
            U32 delta_value = value - prior_value0 + 0x80808080;
            prior_value0 = value;
            symbol_counts0[delta_value & 0xFF]++;
            symbol_counts0[(delta_value >> 8) & 0xFF]++;
            symbol_counts0[(delta_value >> 16) & 0xFF]++;
            symbol_counts0[delta_value >> 24]++;
            value = (*(in_char_ptr + 3) << 24) + (*(in_char_ptr + 2) << 16) + (*(in_char_ptr + 1) << 8) + *in_char_ptr;
            delta_value = value - prior_value1 + 0x80808080;
            prior_value1 = value;
            symbol_counts1[delta_value & 0xFF]++;
            symbol_counts1[(delta_value >> 8) & 0xFF]++;
            symbol_counts1[(delta_value >> 16) & 0xFF]++;
            symbol_counts1[delta_value >> 24]++;
            in_char_ptr += 4;
          }
          while (in_char_ptr < end_char_ptr) {
            symbol_counts0[(U8)(*in_char_ptr - *(in_char_ptr-4))]++;
            symbol_counts1[(U8)(*in_char_ptr - *(in_char_ptr-4))]++;
            in_char_ptr++;
          }
          order_0_entropy1 = log2((double)num_in_char) * (double)num_in_char;
          order_0_entropy2 = order_0_entropy1;
          for (i = 0 ; i < 0x100 ; i++) {
            if (symbol_counts0[i]) {
              double d_count = (double)symbol_counts0[i];
              order_0_entropy1 -= d_count * log2(d_count);
            }
            if (symbol_counts1[i]) {
              double d_count = (double)symbol_counts1[i];
              order_0_entropy2 -= d_count * log2(d_count);
            }
          }
          if ((order_0_entropy1 < min_entropy) && (order_0_entropy1 < order_0_entropy2)) {
            fprintf(stderr,"Big endian\n");
            fputc(0x28, fd_out);
            in_char_ptr = in_char + ((end_char_ptr - in_char - 8) & ~3);
            U32 value = (*(in_char_ptr + 4) << 24) + (*(in_char_ptr + 5) << 16)
                + (*(in_char_ptr + 6) << 8) + *(in_char_ptr + 7);
            while (in_char_ptr >= in_char) {
              U32 prior_value = (*in_char_ptr << 24) + (*(in_char_ptr + 1) << 16)
                  + (*(in_char_ptr + 2) << 8) + *(in_char_ptr + 3);
              U32 delta_value = value - prior_value + 0x808080;
              *(in_char_ptr + 4) = (delta_value >> 24) & 0xFF;
              *(in_char_ptr + 5) = (delta_value >> 16) & 0xFF;
              *(in_char_ptr + 6) = (delta_value >> 8) & 0xFF;
              *(in_char_ptr + 7) = delta_value & 0xFF;
              value = prior_value;
              in_char_ptr -= 4;
            }
          }
          else if (order_0_entropy2 < min_entropy) {
            fprintf(stderr,"Little endian\n");
            fputc(0xA8, fd_out);
            in_char_ptr = in_char + ((end_char_ptr - in_char - 8) & ~3);
            U32 value = (*(in_char_ptr + 7) << 24) + (*(in_char_ptr + 6) << 16)
                + (*(in_char_ptr + 5) << 8) + *(in_char_ptr + 4);
            while (in_char_ptr >= in_char) {
              U32 prior_value = (*(in_char_ptr + 3) << 24) + (*(in_char_ptr + 2) << 16)
                  + (*(in_char_ptr + 1) << 8) + *in_char_ptr;
              U32 delta_value = value - prior_value + 0x808080;
              *(in_char_ptr + 7) = (delta_value >> 24) & 0xFF;
              *(in_char_ptr + 6) = (delta_value >> 16) & 0xFF;
              *(in_char_ptr + 5) = (delta_value >> 8) & 0xFF;
              *(in_char_ptr + 4) = delta_value & 0xFF;
              value = prior_value;
              in_char_ptr -= 4;
            }
          }
          else {
            fprintf(stderr,"No carry\n");
            fputc(8, fd_out);
            in_char_ptr = end_char_ptr - 4;
            while (--in_char_ptr >= in_char)
              *(in_char_ptr + 4) -= *in_char_ptr;
          }
        }
      }
      else {
        fprintf(stderr,"No carry\n");
        fputc(8, fd_out);
        in_char_ptr = end_char_ptr - 4;
        while (--in_char_ptr >= in_char)
          *(in_char_ptr + 4) -= *in_char_ptr;
      }
    }

    if ((stride == 2) || (stride == 4)) {
      U8 * in_char2 = (uint8_t *)malloc(CHARS_TO_WRITE); // SHOULD FREE!!
      U8 * in_char2_ptr;
      U8 * start_block_ptr = in_char;
      U8 * end_block_ptr = start_block_ptr + CHARS_TO_WRITE;
      if (stride == 2) {
        while (end_block_ptr < end_char_ptr) {
          in_char2_ptr = in_char2;
          in_char_ptr = start_block_ptr + 1;
          while (in_char_ptr < end_block_ptr) {
            *in_char2_ptr++ = *in_char_ptr;
            in_char_ptr += 2;
          }
          in_char2_ptr = start_block_ptr;
          in_char_ptr = start_block_ptr;
          while (in_char_ptr < end_block_ptr) {
            *in_char2_ptr++ = *in_char_ptr;
            in_char_ptr += 2;
          }
          in_char_ptr = in_char2;
          while (in_char2_ptr < end_block_ptr)
            *in_char2_ptr++ = *in_char_ptr++;
          start_block_ptr = end_block_ptr;
          end_block_ptr += CHARS_TO_WRITE;
        }
        in_char2_ptr = in_char2;
        in_char_ptr = start_block_ptr + 1;
        while (in_char_ptr < end_char_ptr) {
          *in_char2_ptr++ = *in_char_ptr;
          in_char_ptr += 2;
        }
        in_char2_ptr = start_block_ptr;
        in_char_ptr = start_block_ptr;
        while (in_char_ptr < end_char_ptr) {
          *in_char2_ptr++ = *in_char_ptr;
          in_char_ptr += 2;
        }
        in_char_ptr = in_char2;
        while (in_char2_ptr < end_char_ptr)
          *in_char2_ptr++ = *in_char_ptr++;
      }
      else {
        while (end_block_ptr < end_char_ptr) {
          in_char2_ptr = in_char2;
          in_char_ptr = start_block_ptr + 1;
          while (in_char_ptr < end_block_ptr) {
            *in_char2_ptr++ = *in_char_ptr;
            in_char_ptr += 4;
          }
          in_char_ptr = start_block_ptr + 2;
          while (in_char_ptr < end_block_ptr) {
            *in_char2_ptr++ = *in_char_ptr;
            in_char_ptr += 4;
          }
          in_char_ptr = start_block_ptr + 3;
          while (in_char_ptr < end_block_ptr) {
            *in_char2_ptr++ = *in_char_ptr;
            in_char_ptr += 4;
          }
          in_char2_ptr = start_block_ptr;
          in_char_ptr = start_block_ptr;
          while (in_char_ptr < end_block_ptr) {
            *in_char2_ptr++ = *in_char_ptr;
            in_char_ptr += 4;
          }
          in_char_ptr = in_char2;
          while (in_char2_ptr < end_block_ptr)
            *in_char2_ptr++ = *in_char_ptr++;
          start_block_ptr = end_block_ptr;
          end_block_ptr += CHARS_TO_WRITE;
        }
        in_char2_ptr = in_char2;
        in_char_ptr = start_block_ptr + 1;
        while (in_char_ptr < end_char_ptr) {
          *in_char2_ptr++ = *in_char_ptr;
          in_char_ptr += 4;
        }
        in_char_ptr = start_block_ptr + 2;
        while (in_char_ptr < end_char_ptr) {
          *in_char2_ptr++ = *in_char_ptr;
          in_char_ptr += 4;
        }
        in_char_ptr = start_block_ptr + 3;
        while (in_char_ptr < end_char_ptr) {
          *in_char2_ptr++ = *in_char_ptr;
          in_char_ptr += 4;
        }
        in_char_ptr = start_block_ptr;
        in_char2_ptr = start_block_ptr;
        while (in_char_ptr < end_char_ptr) {
          *in_char2_ptr++ = *in_char_ptr;
          in_char_ptr += 4;
        }
        in_char_ptr = in_char2;
        while (in_char2_ptr < end_char_ptr)
          *in_char2_ptr++ = *in_char_ptr++;
      }

      in_char_ptr = in_char;
      while (in_char_ptr != end_char_ptr) {
        if (*in_char_ptr >= 0xFE) {
          *out_char_ptr++ = *in_char_ptr++;
          *out_char_ptr++ = 0xFF;
        }
        else
          *out_char_ptr++ = *in_char_ptr++;

        if (out_char_ptr - out_char_buffer >= CHARS_TO_WRITE) {
          fwrite(out_char_buffer, 1, out_char_ptr - out_char_buffer, fd_out);
          num_out_char += out_char_ptr - out_char_buffer;
          out_char_ptr = out_char_buffer;
          fflush(fd_out);
        }
      }
    }
    else {
      in_char_ptr = in_char;
      while (in_char_ptr != end_char_ptr) {
        if (*in_char_ptr >= 0xFE) {
          *out_char_ptr++ = *in_char_ptr++;
          *out_char_ptr++ = 0xFF;
        }
        else
          *out_char_ptr++ = *in_char_ptr++;

        if (out_char_ptr - out_char_buffer >= CHARS_TO_WRITE) {
          fwrite(out_char_buffer, 1, out_char_ptr - out_char_buffer, fd_out);
          num_out_char += out_char_ptr - out_char_buffer;
          out_char_ptr = out_char_buffer;
          fflush(fd_out);
        }
      }
    }
  }
  else {
    fprintf(stderr,"Converting data\n");
    fputc(0,fd_out);
    in_char_ptr = in_char;
    while (in_char_ptr != end_char_ptr) {
      if (*in_char_ptr >= 0xFE) {
        *out_char_ptr++ = *in_char_ptr++;
        *out_char_ptr++ = 0xFF;
      }
      else
        *out_char_ptr++ = *in_char_ptr++;

      if (out_char_ptr - out_char_buffer >= CHARS_TO_WRITE) {
        fwrite(out_char_buffer, 1, out_char_ptr - out_char_buffer, fd_out);
        num_out_char += out_char_ptr - out_char_buffer;
        out_char_ptr = out_char_buffer;
        fflush(fd_out);
      }
    }
  }

  fwrite(out_char_buffer, 1, out_char_ptr - out_char_buffer, fd_out);
  num_out_char += out_char_ptr - out_char_buffer;
  fclose(fd_out);
  fprintf(stderr,"Wrote 1 byte header and %u data bytes in %.3f seconds.\n",
      num_out_char,(float)(clock()-start_time)/CLOCKS_PER_SEC);
  return(0);
}