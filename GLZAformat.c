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

// GLZAformat.c
//   Adds 0xFF after all 0xFE and 0xFF bytes to support compressions insert and define symbols
//   Replaces 'A' - 'Z' with 0xFF 'C' followed by the corresponding lower case letter when text detected
//   For non-text files, checks order 0 entropy of delta coding options and delta codes if better
//
// Usage:
//   GLZAformat <infilename> <outfilename>


#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>

const CAP_CHAR = 0x43;
const CHARS_TO_WRITE = 4000000;
unsigned char in_char[1050000000];
unsigned char out_char_buffer[4000100];

int main(int argc, char* argv[])
{
  unsigned char *in_char_ptr, *end_char_ptr, *out_char_ptr, this_char, prev_char, next_char;
  unsigned int num_in_char, num_out_char, i;
  unsigned int num_AZ, num_az_pre_AZ, num_az_post_AZ;
  unsigned int e0_counts[0x100], e1_counts[0x100], e2_counts[0x100], e4_counts[0x100];
  double order_0_entropy0, order_0_entropy1, order_0_entropy2, order_0_entropy4;
  unsigned long long int start_time;
  FILE *fd_in, *fd_out;


  start_time = clock();

  if ((fd_in = fopen(argv[1],"rb"))==NULL) {
    printf("fopen error - fd_in\n");
    exit(0);
  }
  if ((fd_out = fopen(argv[2],"wb"))==NULL) {
    printf("fopen error - fd_out\n");
    exit(0);
  }

  fseek(fd_in, 0, SEEK_END);
  num_in_char = ftell(fd_in);
  rewind(fd_in);
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

  if (num_in_char > 1) {
    in_char_ptr = in_char;
    this_char = *in_char_ptr++;
    e0_counts[this_char]++;
    e1_counts[this_char]++;
    e2_counts[this_char]++;
    e4_counts[this_char]++;
    prev_char = this_char;
    if ((this_char >= 'A') && (this_char <= 'Z')) {
      num_AZ++;
      next_char = *in_char_ptr;
      if ((next_char >= 'a') && (next_char <= 'z'))
        num_az_post_AZ++;
    }
    while (in_char_ptr != end_char_ptr - 1) {
      this_char = *in_char_ptr++;
      if (in_char_ptr - in_char >= 5) {
        e0_counts[this_char]++;
        e1_counts[(unsigned char)(this_char - *(in_char_ptr-2))]++;
        e2_counts[(unsigned char)(this_char - *(in_char_ptr-3))]++;
        e4_counts[(unsigned char)(this_char - *(in_char_ptr-5))]++;
      }
      else if (in_char_ptr - in_char >= 3) {
        e0_counts[this_char]++;
        e1_counts[(unsigned char)(this_char - *(in_char_ptr-2))]++;
        e2_counts[(unsigned char)(this_char - *(in_char_ptr-3))]++;
        e4_counts[this_char]++;
      }
      else if (in_char_ptr - in_char >= 2) {
        e0_counts[this_char]++;
        e1_counts[(unsigned char)(this_char - *(in_char_ptr-2))]++;
        e2_counts[this_char]++;
        e4_counts[this_char]++;
      }
      else {
        e0_counts[this_char]++;
        e1_counts[this_char]++;
        e2_counts[this_char]++;
        e4_counts[this_char]++;
      }

      if ((this_char >= 'A') && (this_char <= 'Z')) {
        num_AZ++;
        next_char = *in_char_ptr;
        if ((next_char >= 'a') && (next_char <= 'z'))
          num_az_post_AZ++;
        if ((prev_char >= 'a') && (prev_char <= 'z'))
          num_az_pre_AZ++;
      }
      prev_char = this_char;
    }
    if (in_char_ptr - in_char >= 4) {
      e0_counts[*in_char_ptr]++;
      e1_counts[(unsigned char)(*in_char_ptr - *(in_char_ptr-1))]++;
      e2_counts[(unsigned char)(*in_char_ptr - *(in_char_ptr-2))]++;
      e4_counts[(unsigned char)(*in_char_ptr - *(in_char_ptr-4))]++;
    }
    else if (in_char_ptr - in_char >= 2) {
      e0_counts[*in_char_ptr]++;
      e1_counts[(unsigned char)(*in_char_ptr - *(in_char_ptr-1))]++;
      e2_counts[(unsigned char)(*in_char_ptr - *(in_char_ptr-2))]++;
      e4_counts[*in_char_ptr]++;
    }
    else if (in_char_ptr - in_char >= 1) {
      e0_counts[*in_char_ptr]++;
      e1_counts[(unsigned char)(*in_char_ptr - *(in_char_ptr-1))]++;
      e2_counts[*in_char_ptr]++;
      e4_counts[*in_char_ptr]++;
    }
    else {
      e0_counts[*in_char_ptr]++;
      e1_counts[*in_char_ptr]++;
      e2_counts[*in_char_ptr]++;
      e4_counts[*in_char_ptr]++;
    }
    if ((this_char >= 'A') && (this_char <= 'Z')) {
      num_AZ++;
      next_char = *in_char_ptr;
      if ((prev_char >= 'a') && (prev_char <= 'z'))
        num_az_pre_AZ++;
    }
  }

  in_char_ptr = in_char;
  out_char_ptr = out_char_buffer;
  num_out_char = 0;

  if ((num_AZ > (num_in_char >> 10)) && (2 * num_az_post_AZ > num_AZ) && (num_az_post_AZ > 10 * num_az_pre_AZ)) {
    printf("Pre and capital encoding %u bytes\n",num_in_char);
    fputc(1,fd_out);
    while (in_char_ptr != end_char_ptr) {
      if (((int)*in_char_ptr >= (int)'A') && ((int)*in_char_ptr <= (int)'Z')) {
        *out_char_ptr++ = CAP_CHAR;
        *out_char_ptr++ = *in_char_ptr++ + ('a' - 'A');
      }
      else if (*in_char_ptr >= 0xFE) {
        *out_char_ptr++ = *in_char_ptr++;
        *out_char_ptr++ = 0xFF;
      }
      else
        *out_char_ptr++ = *in_char_ptr++;

      if (out_char_ptr - out_char_buffer > CHARS_TO_WRITE) {
        fwrite(out_char_buffer, 1, out_char_ptr - out_char_buffer, fd_out);
        num_out_char += out_char_ptr - out_char_buffer;
        out_char_ptr = out_char_buffer;
        fflush(fd_out);
      }
    }
  }
  else {
    printf("Pre encoding %u bytes\n",num_in_char);
    if (in_char_ptr != end_char_ptr) {
      double log_num_tokens = log((double)(end_char_ptr - in_char_ptr));
      order_0_entropy0 = 0.0; order_0_entropy1 = 0.0; order_0_entropy2 = 0.0; order_0_entropy4 = 0.0;
      for (i = 0 ; i < 0x100 ; i++) {
        if (e0_counts[i]) {
          double d_count = (double)e0_counts[i];
          order_0_entropy0 -= d_count * (log(d_count) - log_num_tokens);
        }
        if (e1_counts[i]) {
          double d_count = (double)e1_counts[i];
          order_0_entropy1 -= d_count * (log(d_count) - log_num_tokens);
        }
        if (e2_counts[i]) {
          double d_count = (double)e2_counts[i];
          order_0_entropy2 -= d_count * (log(d_count) - log_num_tokens);
        }
        if (e4_counts[i]) {
          double d_count = (double)e4_counts[i];
          order_0_entropy4 -= d_count * (log(d_count) - log_num_tokens);
        }
      }
      double e_adj = 1.0 / (log(2.0) * (double)(end_char_ptr - in_char_ptr));
      order_0_entropy0 *= e_adj;
      order_0_entropy1 *= e_adj;
      order_0_entropy2 *= e_adj;
      order_0_entropy4 *= e_adj;
    }
    double min_entropy = order_0_entropy0;
    char delta_gap = 0;
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

    fputc(delta_gap * 2, fd_out);
    if (delta_gap) {
      unsigned char * tp = end_char_ptr;
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

      if (out_char_ptr - out_char_buffer > CHARS_TO_WRITE) {
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
  printf("Wrote 1 byte header and %u encoded bytes in %.3f seconds.\n",num_out_char,0.001*(float)(clock()-start_time));
}
