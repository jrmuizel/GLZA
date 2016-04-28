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
//   Adds 0xFF after all 0xFE and 0xFF bytes to support compressions insert and define symbols
//   Replaces 'A' - 'Z' with 0xFF 'C' followed by the corresponding lower case letter when text detected
//   For non-text files, checks order 0 entropy of delta coding options and delta codes if better
//
//   Checks order 0 entropy of standard coding vs. delta coding for 1, 2 and 4 byte values (entire file).
//   Delta transforms data when appropriate
//
// Usage:
//   GLZAformat <infilename> <outfilename>


#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include "GLZA.h"

const U8 CAP_CHAR = 0x43;
const U32 CHARS_TO_WRITE = 4000000;
U8 * in_char;
U8 out_char_buffer[4000100];


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
  U8 *in_char_ptr, *end_char_ptr, *out_char_ptr, this_char, prev_char, next_char;
  U32 num_in_char, num_out_char, i;
  U32 num_AZ, num_az_pre_AZ, num_az_post_AZ;
  U32 e0_counts[0x100], e1_counts[0x100], e2_counts[0x100], e4_counts[0x100];
  clock_t start_time;
  double order_0_entropy0, order_0_entropy1, order_0_entropy2, order_0_entropy4;


  start_time = clock();

  if (argc != 3) {
    fprintf(stderr,"ERROR - Command format is not \"GLZAformat <infile> <outfile>\"\n");
    exit(0);
  }
  if ((fd_in = fopen(argv[1],"rb"))==NULL) {
    fprintf(stderr,"ERROR - Unable to open input file '%s'\n",argv[1]);
    exit(0);
  }
  if ((fd_out = fopen(argv[2],"wb"))==NULL) {
    fprintf(stderr,"ERROR - Unable to open output file '%s'\n",argv[2]);
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
    e0_counts[i] = 0;
    e1_counts[i] = 0;
    e2_counts[i] = 0;
    e4_counts[i] = 0;
  }

  if (num_in_char > 4) {
    in_char_ptr = in_char;
    this_char = *in_char_ptr++;
    e0_counts[this_char]++;
    e1_counts[this_char]++;
    e2_counts[this_char]++;
    e4_counts[this_char]++;
    if ((this_char >= 'A') && (this_char <= 'Z')) {
      num_AZ++;
      next_char = *in_char_ptr;
      if (((next_char >= 'a') && (next_char <= 'z')) || ((next_char >= 'A') && (next_char <= 'Z')))
        num_az_post_AZ++;
    }

    this_char = *in_char_ptr++;
    e0_counts[this_char]++;
    e1_counts[(unsigned char)(this_char - *(in_char_ptr-2))]++;
    e2_counts[this_char]++;
    e4_counts[this_char]++;
    update_capital_statistics();

    this_char = *in_char_ptr++;
    e0_counts[this_char]++;
    e1_counts[(unsigned char)(this_char - *(in_char_ptr-2))]++;
    e2_counts[(unsigned char)(this_char - *(in_char_ptr-3))]++;
    e4_counts[this_char]++;
    update_capital_statistics();

    this_char = *in_char_ptr++;
    e0_counts[this_char]++;
    e1_counts[(unsigned char)(this_char - *(in_char_ptr-2))]++;
    e2_counts[(unsigned char)(this_char - *(in_char_ptr-3))]++;
    e4_counts[this_char]++;
    update_capital_statistics();

    while (in_char_ptr != end_char_ptr) {
      this_char = *in_char_ptr++;
      e0_counts[this_char]++;
      e1_counts[(unsigned char)(this_char - *(in_char_ptr-2))]++;
      e2_counts[(unsigned char)(this_char - *(in_char_ptr-3))]++;
      e4_counts[(unsigned char)(this_char - *(in_char_ptr-5))]++;
      update_capital_statistics();
    }
  }

  in_char_ptr = in_char;
  out_char_ptr = out_char_buffer;
  num_out_char = 0;

  if (num_AZ && (2 * num_az_post_AZ > num_AZ) && (2 * num_az_post_AZ > 3 * num_az_pre_AZ)) {
    fprintf(stderr,"Converting textual data\n");
    fputc(1,fd_out);
    while (in_char_ptr != end_char_ptr) {
      if ((*in_char_ptr >= 'A') && (*in_char_ptr <= 'Z')) {
        *out_char_ptr++ = CAP_CHAR;
        *out_char_ptr++ = *in_char_ptr++ + ('a' - 'A');
      }
      else if (*in_char_ptr >= 0xFE) {
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
    if (in_char_ptr != end_char_ptr) {
      order_0_entropy0 = log2((double)num_in_char) * (double)num_in_char;
      order_0_entropy1 = order_0_entropy0;
      order_0_entropy2 = order_0_entropy0;
      order_0_entropy4 = order_0_entropy0;
      for (i = 0 ; i < 0x100 ; i++) {
        if (e0_counts[i]) {
          double d_count = (double)e0_counts[i];
          order_0_entropy0 -= d_count * log2(d_count);
        }
        if (e1_counts[i]) {
          double d_count = (double)e1_counts[i];
          order_0_entropy1 -= d_count * log2(d_count);
        }
        if (e2_counts[i]) {
          double d_count = (double)e2_counts[i];
          order_0_entropy2 -= d_count * log2(d_count);
        }
        if (e4_counts[i]) {
          double d_count = (double)e4_counts[i];
          order_0_entropy4 -= d_count * log2(d_count);
        }
      }
      double min_entropy = order_0_entropy0;
      U8 delta_gap = 0;
      if (order_0_entropy1 < min_entropy) {
        min_entropy = order_0_entropy1;
        delta_gap = 1;
      }
      if (order_0_entropy2 < min_entropy) {
        min_entropy = order_0_entropy2;
        delta_gap = 2;
      }
      if (order_0_entropy4 < min_entropy)
        delta_gap = 4;

      if (delta_gap)
        fprintf(stderr,"Applying %u byte delta transformation\n",(unsigned int)delta_gap);
      fprintf(stderr,"Converting data\n");
      fputc(delta_gap * 2, fd_out);
      if (delta_gap) {
        U8 * tp = end_char_ptr;
        while (--tp >= in_char_ptr + delta_gap)
          *tp -= *(tp - delta_gap);
      }
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
  fwrite(out_char_buffer, 1, out_char_ptr - out_char_buffer, fd_out);
  num_out_char += out_char_ptr - out_char_buffer;
  fclose(fd_out);
  fprintf(stderr,"Wrote 1 byte header and %u data bytes in %.3f seconds.\n",
      num_out_char,(float)(clock()-start_time)/CLOCKS_PER_SEC);
  return(0);
}
