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
//   For non-text files, checks order 1 entropy of standard coding vs. delta coding for strides
//   1 - 100 (global).  Delta transforms data when appropriate.
//
// Usage:
//   GLZAformat [-c#] [-d#] [-l#] <infilename> <outfilename>, where
//       -c0 disables capital encoding
//       -c1 forces text processing and capital encoding
//       -d0 disables delta encoding
//       -l0 disables capital lock encoding


#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

const uint32_t CHARS_TO_WRITE = 0x40000;
uint8_t * in_char;
uint8_t out_char_buffer[0x40010];


void clear_counts(uint32_t symbol_counts[0x100], uint32_t order_1_counts[0x100][0x100]) {
  uint8_t i = 0xFF;
  do {
    symbol_counts[i] = 0;
    uint8_t j = 0xFF;
    do {
      order_1_counts[i][j] = 0;
    } while (j-- != 0);
  } while (i-- != 0);
  return;
}


double calculate_order_1_entropy(uint32_t symbol_counts[0x100], uint32_t order_1_counts[0x100][0x100]) {
  uint16_t i, j;
  uint16_t num_symbols = 0;
  double entropy = 0.0;
  for (i = 0 ; i < 0x100 ; i++) {
    if (symbol_counts[i] != 0) {
      num_symbols++;
      entropy += (double)symbol_counts[i] * log2((double)symbol_counts[i]);
      for (j = 0 ; j < 0x100 ; j++) {
        if (order_1_counts[i][j]) {
          double d_count = (double)order_1_counts[i][j];
          entropy -= d_count * log2(d_count);
        }
      }
    }
  }
  entropy += (double)num_symbols * (log2((double)num_symbols) + 11.0);
  return(entropy);
}


void print_usage() {
  fprintf(stderr,"ERROR - Invalid format - Use GLZAformat [-c#] [-d#] [-l#] <infile> <outfile>\n");
  fprintf(stderr," where -c0 disables capital encoding\n");
  fprintf(stderr,"       -c1 forces capital encoding\n");
  fprintf(stderr,"       -d0 disables delta coding\n");
  fprintf(stderr,"       -l0 disables capital lock encoding\n");
  return;
}


int main(int argc, char* argv[])
{
  FILE *fd_in, *fd_out;
  uint8_t this_char, prev_char, next_char, user_cap_encoded, user_cap_lock_encoded, user_delta_encoded, stride;
  uint8_t *in_char_ptr, *end_char_ptr, *out_char_ptr;
  uint32_t num_in_char, num_out_char, i, j, k;
  uint32_t num_AZ, num_az_pre_AZ, num_az_post_AZ, num_spaces;
  uint32_t order_1_counts[0x100][0x100];
  uint32_t symbol_counts[0x100];
  int32_t arg_num;
  double order_1_entropy, best_stride_entropy, saved_entropy[4];
  clock_t start_time;

  // format byte: B0: cap encoded, B3:B1 = stride (0 - 4), B5:B4 = log2 delta length (0 - 2), B6: little endian


  start_time = clock();

  user_cap_encoded = 0;
  user_cap_lock_encoded = 0;
  user_delta_encoded = 0;

  arg_num = 1;
  while (*argv[arg_num] ==  '-') {
    if (*(argv[arg_num] + 1) == 'c') {
      user_cap_encoded = 1 + *(argv[arg_num++] + 2) - '0';
      if ((user_cap_encoded < 1) || (user_cap_encoded > 2)) {
        fprintf(stderr,"ERROR: -c value must be 0 or 1\n");
        exit(EXIT_FAILURE);
      }
    }
    else if (*(argv[arg_num] + 1) == 'd') {
      user_delta_encoded = 1 + *(argv[arg_num++] + 2) - '0';
      if ((user_delta_encoded < 1) || (user_delta_encoded > 2)) {
        fprintf(stderr,"ERROR: -d value must be 0 or 1\n");
        exit(EXIT_FAILURE);
      }
    }
    else if (*(argv[arg_num] + 1) == 'l') {
      user_cap_lock_encoded = 1 + *(argv[arg_num++] + 2) - '0';
      if ((user_cap_lock_encoded < 1) || (user_cap_lock_encoded > 2)) {
        fprintf(stderr,"ERROR: -l value must be 0 or 1\n");
        exit(EXIT_FAILURE);
      }
    }
    else {
      fprintf(stderr,"ERROR - Invalid '-' format.  Only -c<value>, -d<value> and -l<value> allowed\n");
      exit(EXIT_FAILURE);
    }
  }

  if (argc != arg_num + 2) {
    fprintf(stderr,"ERROR - Command format is \"GLZAformat [-c#] [-d#] [-l0] <infile> <outfile>\"\n");
    exit(EXIT_FAILURE);
  }
  if ((fd_in = fopen(argv[arg_num],"rb"))==NULL) {
    fprintf(stderr,"ERROR - Unable to open input file '%s'\n",argv[arg_num]);
    exit(EXIT_FAILURE);
  }
  if ((fd_out = fopen(argv[++arg_num],"wb"))==NULL) {
    fprintf(stderr,"ERROR - Unable to open output file '%s'\n",argv[arg_num]);
    exit(EXIT_FAILURE);
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
  num_spaces = 0;

  if (num_in_char > 4) {
    in_char_ptr = in_char;
    this_char = *in_char_ptr++;
    if (this_char == 0x20)
      num_spaces++;
    if ((this_char >= 'A') && (this_char <= 'Z')) {
      num_AZ++;
      next_char = *in_char_ptr;
      if (((next_char >= 'a') && (next_char <= 'z')) || ((next_char >= 'A') && (next_char <= 'Z')))
        num_az_post_AZ++;
    }

    while (in_char_ptr != end_char_ptr) {
      this_char = *in_char_ptr++;
      if (this_char == 0x20)
        num_spaces++;
      if ((this_char >= 'A') && (this_char <= 'Z')) {
        num_AZ++;
        prev_char = *(in_char_ptr - 2);
        next_char = *in_char_ptr;
        if (((next_char >= 'a') && (next_char <= 'z')) || ((next_char >= 'A') && (next_char <= 'Z')))
          num_az_post_AZ++;
        if (((prev_char >= 'a') && (prev_char <= 'z')) || ((prev_char >= 'A') && (prev_char <= 'Z')))
          num_az_pre_AZ++;
      }
    }
  }

  out_char_ptr = out_char_buffer;
  num_out_char = 0;

  if (((num_AZ && (4 * num_az_post_AZ > num_AZ) && (num_az_post_AZ > num_az_pre_AZ)
      && (num_spaces > num_in_char / 50)) && (user_cap_encoded != 1)) || (user_cap_encoded == 2)) {
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
    clear_counts(symbol_counts, order_1_counts);
    for (i = 0 ; i < num_in_char - 1 ; i++) {
      symbol_counts[in_char[i]]++;
      order_1_counts[in_char[i]][in_char[i+1]]++;
    }
    symbol_counts[in_char[num_in_char-1]]++;
    order_1_counts[in_char[num_in_char-1]][0x80]++;
    order_1_entropy = calculate_order_1_entropy(symbol_counts, order_1_counts);
    best_stride_entropy = order_1_entropy;
    stride = 0;

    for (k = 1 ; k <= 100 ; k++) {
      if (num_in_char <= k)
        break;
      clear_counts(symbol_counts, order_1_counts);
      if ((k == 2) | (k == 4)) {
        for (i = 0 ; i < k  ; i++) {
          symbol_counts[in_char[i]]++;
          order_1_counts[in_char[i]][0xFF & (in_char[i+k] - in_char[i])]++;
        }
        for (i = k ; i < num_in_char - k ; i++) {
          symbol_counts[0xFF & (in_char[i] - in_char[i-k])]++;
          order_1_counts[0xFF & (in_char[i] - in_char[i-k])][0xFF & (in_char[i+k] - in_char[i])]++;
        }
        for (i = num_in_char - k ; i < num_in_char ; i++) {
          symbol_counts[0xFF & (in_char[i] - in_char[i-k])]++;
          order_1_counts[0xFF & (in_char[i] - in_char[i-k])][0x80]++;
        }
        order_1_entropy = calculate_order_1_entropy(symbol_counts, order_1_counts);
        if ((order_1_entropy < 0.95 * best_stride_entropy) || ((stride != 0) && (order_1_entropy < best_stride_entropy))) {
          stride = k;
          best_stride_entropy = order_1_entropy;
        }
      }
      else {
        for (i = 0 ; i < k - 1 ; i++) {
          symbol_counts[in_char[i]]++;
          order_1_counts[in_char[i]][in_char[i+1]]++;
        }
        symbol_counts[in_char[k-1]]++;
        order_1_counts[in_char[k-1]][0xFF & (in_char[k]-in_char[0])]++;
        uint8_t failed_test = 0;
        i = k;
        if (num_in_char > 100000) {
          uint32_t initial_test_size = 100000 + ((num_in_char - 100000) >> 3);
          while (i < initial_test_size) {
            symbol_counts[0xFF & (in_char[i] - in_char[i-k])]++;
            order_1_counts[0xFF & (in_char[i] - in_char[i-k])][0xFF & (in_char[i+1] - in_char[i+1-k])]++;
            i++;
          }
          order_1_entropy = calculate_order_1_entropy(symbol_counts, order_1_counts);
          if (order_1_entropy >= 1.05 * best_stride_entropy * (double)initial_test_size / (double)num_in_char)
            failed_test = 1;
        }
        if (failed_test == 0) {
          while (i < num_in_char - 1) {
            symbol_counts[0xFF & (in_char[i] - in_char[i-k])]++;
            order_1_counts[0xFF & (in_char[i] - in_char[i-k])][0xFF & (in_char[i+1] - in_char[i+1-k])]++;
            i++;
          }
          symbol_counts[0xFF & (in_char[num_in_char-1] - in_char[num_in_char-1-k])]++;
          order_1_counts[0xFF & (in_char[num_in_char-1] - in_char[num_in_char-1-k])][0x80]++;
          order_1_entropy = calculate_order_1_entropy(symbol_counts, order_1_counts);
          if ((order_1_entropy < 0.95 * best_stride_entropy) || ((stride != 0) && (order_1_entropy < best_stride_entropy))) {
            stride = k;
            best_stride_entropy = order_1_entropy;
          }
        }
      }
    }

    double min_entropy = best_stride_entropy;

    if (stride)
      fprintf(stderr,"Applying %u byte delta transformation\n",(unsigned int)stride);
    else
      fprintf(stderr,"Converting data\n");

    if (stride == 0) {
      fputc(0, fd_out);
    }
    else if (stride == 1) {
      fputc(2, fd_out);
      in_char_ptr = end_char_ptr - 1;
      while (--in_char_ptr >= in_char)
        *(in_char_ptr + 1) -= *in_char_ptr;
    }
    else if (stride == 2) {
      for (j = 0 ; j < 2 ; j++) {
        clear_counts(symbol_counts, order_1_counts);
        symbol_counts[in_char[j]]++;
        order_1_counts[in_char[j]][0xFF & (in_char[j + 2] - in_char[j])]++;
        i = 2 + j;
        while (i < num_in_char - 2) {
          symbol_counts[0xFF & (in_char[i] - in_char[i-2])]++;
          order_1_counts[0xFF & (in_char[i] - in_char[i-2])][0xFF & (in_char[i+2] - in_char[i])]++;
          i += 2;
        }
        symbol_counts[0xFF & (in_char[i] - in_char[i-2])]++;
        order_1_counts[0xFF & (in_char[i] - in_char[i-2])][0]++;
        saved_entropy[j] = calculate_order_1_entropy(symbol_counts, order_1_counts);
      }

      clear_counts(symbol_counts, order_1_counts);
      if (saved_entropy[0] < saved_entropy[1]) {
        // big endian
        uint16_t prior_symbol = (in_char[0] << 8) + in_char[1];
        uint16_t next_symbol = (in_char[2] << 8) + in_char[3];
        uint16_t delta_symbol = next_symbol - prior_symbol + 0x8080;
        uint16_t prior_delta_symbol;
        symbol_counts[in_char[0]]++;
        order_1_counts[in_char[0]][delta_symbol >> 8]++;
        symbol_counts[in_char[1]]++;
        order_1_counts[in_char[1]][0xFF & delta_symbol]++;
        for (i = 2 ; i < num_in_char - 3 ; i += 2) {
          prior_symbol = next_symbol;
          prior_delta_symbol = delta_symbol;
          next_symbol = (in_char[i+2] << 8) + in_char[i+3];
          delta_symbol = next_symbol - prior_symbol + 0x8080;
          symbol_counts[prior_delta_symbol >> 8]++;
          order_1_counts[prior_delta_symbol >> 8][delta_symbol >> 8]++;
          symbol_counts[0xFF & prior_delta_symbol]++;
          order_1_counts[0xFF & prior_delta_symbol][0xFF & delta_symbol]++;
        }
        if (i == num_in_char - 3) {
          prior_symbol = next_symbol;
          prior_delta_symbol = delta_symbol;
          next_symbol = (in_char[i+2] << 8);
          delta_symbol = next_symbol - prior_symbol + 0x8080;
          symbol_counts[prior_delta_symbol >> 8]++;
          order_1_counts[prior_delta_symbol >> 8][delta_symbol >> 8]++;
          symbol_counts[0xFF & prior_delta_symbol]++;
          order_1_counts[0xFF & prior_delta_symbol][0]++;
          symbol_counts[delta_symbol >> 8]++;
          order_1_counts[delta_symbol >> 8][0]++;
        }
        else {
          prior_delta_symbol = delta_symbol;
          symbol_counts[prior_delta_symbol >> 8]++;
          order_1_counts[prior_delta_symbol >> 8][0]++;
          symbol_counts[0xFF & prior_delta_symbol]++;
          order_1_counts[0xFF & prior_delta_symbol][0]++;
        }
        order_1_entropy = calculate_order_1_entropy(symbol_counts, order_1_counts);
        if (order_1_entropy < best_stride_entropy) {
          fprintf(stderr,"Big endian\n");
          fputc(0x14, fd_out);
          in_char_ptr = in_char + ((end_char_ptr - in_char - 4) & ~1);
          uint16_t value = (*(in_char_ptr + 2) << 8) + *(in_char_ptr + 3);
          while (in_char_ptr >= in_char) {
            uint16_t prior_value = (*in_char_ptr << 8) + *(in_char_ptr + 1);
            uint16_t delta_value = value - prior_value + 0x80;
            *(in_char_ptr + 2) = delta_value >> 8;
            *(in_char_ptr + 3) = delta_value & 0xFF;
            value = prior_value;
            in_char_ptr -= 2;
          }
        }
        else {
          fprintf(stderr,"No carry\n");
          fputc(4, fd_out);
          in_char_ptr = end_char_ptr - 2;
          while (--in_char_ptr >= in_char)
            *(in_char_ptr + 2) -= *in_char_ptr;
        }
      }
      else {
        uint16_t prior_symbol = (in_char[1] << 8) + in_char[0];
        uint16_t next_symbol = (in_char[3] << 8) + in_char[2];
        uint16_t delta_symbol = next_symbol - prior_symbol + 0x8080;
        uint16_t prior_delta_symbol;
        symbol_counts[in_char[0]]++;
        order_1_counts[in_char[0]][0xFF & delta_symbol]++;
        symbol_counts[in_char[1]]++;
        order_1_counts[in_char[1]][delta_symbol >> 8]++;
        for (i = 2 ; i < num_in_char - 3 ; i += 2) {
          prior_symbol = next_symbol;
          prior_delta_symbol = delta_symbol;
          next_symbol = (in_char[i+3] << 8) + in_char[i+2];
          delta_symbol = next_symbol - prior_symbol + 0x8080;
          symbol_counts[0xFF & prior_delta_symbol]++;
          order_1_counts[0xFF & prior_delta_symbol][0xFF & delta_symbol]++;
          symbol_counts[prior_delta_symbol >> 8]++;
          order_1_counts[prior_delta_symbol >> 8][delta_symbol >> 8]++;
        }
        if (i == num_in_char - 3) {
          prior_symbol = next_symbol;
          prior_delta_symbol = delta_symbol;
          next_symbol = in_char[i+2];
          delta_symbol = next_symbol - prior_symbol + 0x8080;
          symbol_counts[0xFF & prior_delta_symbol]++;
          order_1_counts[0xFF & prior_delta_symbol][0xFF & delta_symbol]++;
          symbol_counts[prior_delta_symbol >> 8]++;
          order_1_counts[prior_delta_symbol >> 8][0]++;
          symbol_counts[0xFF & delta_symbol]++;
          order_1_counts[0xFF & delta_symbol][0]++;
        }
        else {
          prior_delta_symbol = delta_symbol;
          symbol_counts[0xFF & prior_delta_symbol]++;
          order_1_counts[0xFF & prior_delta_symbol][0]++;
          symbol_counts[prior_delta_symbol >> 8]++;
          order_1_counts[prior_delta_symbol >> 8][0]++;
        }
        order_1_entropy = calculate_order_1_entropy(symbol_counts, order_1_counts);
        if (order_1_entropy < best_stride_entropy) {
          fprintf(stderr,"Little endian\n");
          fputc(0x34, fd_out);
          in_char_ptr = in_char + ((end_char_ptr - in_char - 4) & ~1);
          uint16_t value = (*(in_char_ptr + 3) << 8) + *(in_char_ptr + 2);
          while (in_char_ptr >= in_char) {
            uint16_t prior_value = (*(in_char_ptr + 1) << 8) + *in_char_ptr;
            uint16_t delta_value = value - prior_value + 0x80;
            *(in_char_ptr + 2) = delta_value & 0xFF;
            *(in_char_ptr + 3) = (delta_value >> 8);
            value = prior_value;
            in_char_ptr -= 2;
          }
        }
        else {
          fprintf(stderr,"No carry\n");
          fputc(4, fd_out);
          in_char_ptr = end_char_ptr - 2;
          while (--in_char_ptr >= in_char)
            *(in_char_ptr + 2) -= *in_char_ptr;
        }
      }
    }
    else if (stride == 4) {
      for (k = 0 ; k < 4 ; k++) {
        clear_counts(symbol_counts, order_1_counts);
        symbol_counts[in_char[k]]++;
        order_1_counts[in_char[k]][0xFF & (in_char[k+stride] - in_char[k])]++;
        i = k + stride;
        while (i < num_in_char - stride) {
          symbol_counts[0xFF & (in_char[i] - in_char[i-stride])]++;
          order_1_counts[0xFF & (in_char[i] - in_char[i-stride])][0xFF & (in_char[i+stride] - in_char[i])]++;
          i += stride;
        }
        symbol_counts[0xFF & (in_char[i] - in_char[i-stride])]++;
        order_1_counts[0xFF & (in_char[i] - in_char[i-stride])][0]++;
        saved_entropy[k] = calculate_order_1_entropy(symbol_counts, order_1_counts);
      }
      double best_entropy[4];
      uint8_t best_entropy_position[4];
      for (i = 0 ; i < 4 ; i++) {
        best_entropy[i] = saved_entropy[i];
        best_entropy_position[i] = i;
        int8_t j;
        for (j = i - 1 ; j >= 0 ; j--) {
          if (saved_entropy[i] < best_entropy[j]) {
            best_entropy[j+1] = best_entropy[j];
            best_entropy_position[j+1] = best_entropy_position[j];
            best_entropy[j] = saved_entropy[i];
            best_entropy_position[j] = i;
          }
        }
      }

      if (best_entropy[3] > 1.05 * best_entropy[0]) {
        if ((3.0 * best_entropy[1] < best_entropy[0] + best_entropy[2] + best_entropy[3])
            && (((best_entropy_position[0] - best_entropy_position[1]) & 3) == 2)) {
          clear_counts(symbol_counts, order_1_counts);
          if (best_entropy[0] + best_entropy[2] < best_entropy[1] + best_entropy[3]) {
            // big endian
            uint16_t prior_symbol1 = (in_char[0] << 8) + in_char[1];
            uint16_t prior_symbol2 = (in_char[2] << 8) + in_char[3];
            uint16_t next_symbol1 = (in_char[4] << 8) + in_char[5];
            uint16_t next_symbol2 = (in_char[6] << 8) + in_char[7];
            uint16_t delta_symbol1 = next_symbol1 - prior_symbol1 + 0x8080;
            uint16_t delta_symbol2 = next_symbol2 - prior_symbol2 + 0x8080;
            uint16_t prior_delta_symbol1;
            uint16_t prior_delta_symbol2;
            symbol_counts[in_char[0]]++;
            order_1_counts[in_char[0]][delta_symbol1 >> 8]++;
            symbol_counts[in_char[1]]++;
            order_1_counts[in_char[1]][0xFF & delta_symbol1]++;
            symbol_counts[in_char[2]]++;
            order_1_counts[in_char[2]][delta_symbol2 >> 8]++;
            symbol_counts[in_char[3]]++;
            order_1_counts[in_char[3]][0xFF & delta_symbol2]++;
            for (i = 4 ; i < num_in_char - 7 ; i += 4) {
              prior_symbol1 = next_symbol1;
              prior_symbol2 = next_symbol2;
              prior_delta_symbol1 = delta_symbol1;
              prior_delta_symbol2 = delta_symbol2;
              next_symbol1 = (in_char[i+4] << 8) + in_char[i+5];
              next_symbol2 = (in_char[i+6] << 8) + in_char[i+7];
              delta_symbol1 = next_symbol1 - prior_symbol1 + 0x8080;
              delta_symbol2 = next_symbol2 - prior_symbol2 + 0x8080;
              symbol_counts[prior_delta_symbol1 >> 8]++;
              order_1_counts[prior_delta_symbol1 >> 8][delta_symbol1 >> 8]++;
              symbol_counts[0xFF & prior_delta_symbol1]++;
              order_1_counts[0xFF & prior_delta_symbol1][0xFF & delta_symbol1]++;
              symbol_counts[prior_delta_symbol2 >> 8]++;
              order_1_counts[prior_delta_symbol2 >> 8][delta_symbol2 >> 8]++;
              symbol_counts[0xFF & prior_delta_symbol2]++;
              order_1_counts[0xFF & prior_delta_symbol2][0xFF & delta_symbol2]++;
            }
            if (i == num_in_char - 7) {
              prior_symbol1 = next_symbol1;
              prior_symbol2 = next_symbol2;
              prior_delta_symbol1 = delta_symbol1;
              prior_delta_symbol2 = delta_symbol2;
              next_symbol1 = (in_char[i+4] << 8) + in_char[i+5];
              next_symbol2 = in_char[i+6] << 8;
              delta_symbol1 = next_symbol1 - prior_symbol1 + 0x8080;
              delta_symbol2 = next_symbol2 - prior_symbol2 + 0x8080;
              symbol_counts[prior_delta_symbol1 >> 8]++;
              order_1_counts[prior_delta_symbol1 >> 8][delta_symbol1 >> 8]++;
              symbol_counts[0xFF & prior_delta_symbol1]++;
              order_1_counts[0xFF & prior_delta_symbol1][0xFF & delta_symbol1]++;
              symbol_counts[prior_delta_symbol2 >> 8]++;
              order_1_counts[prior_delta_symbol2 >> 8][delta_symbol2 >> 8]++;
              symbol_counts[0xFF & prior_delta_symbol2]++;
              order_1_counts[0xFF & prior_delta_symbol2][0x80]++;
              symbol_counts[delta_symbol1 >> 8]++;
              order_1_counts[delta_symbol1 >> 8][0x80]++;
              symbol_counts[0xFF & delta_symbol1]++;
              order_1_counts[0xFF & delta_symbol1][0x80]++;
              symbol_counts[delta_symbol2 >> 8]++;
              order_1_counts[delta_symbol2 >> 8][0x80]++;
            }
            else if (i == num_in_char - 6) {
              prior_symbol1 = next_symbol1;
              prior_symbol2 = next_symbol2;
              prior_delta_symbol1 = delta_symbol1;
              prior_delta_symbol2 = delta_symbol2;
              next_symbol1 = (in_char[i+4] << 8) + in_char[i+5];
              delta_symbol1 = next_symbol1 - prior_symbol1 + 0x8080;
              symbol_counts[prior_delta_symbol1 >> 8]++;
              order_1_counts[prior_delta_symbol1 >> 8][delta_symbol1 >> 8]++;
              symbol_counts[0xFF & prior_delta_symbol1]++;
              order_1_counts[0xFF & prior_delta_symbol1][0xFF & delta_symbol1]++;
              symbol_counts[prior_delta_symbol2 >> 8]++;
              order_1_counts[prior_delta_symbol2 >> 8][0x80]++;
              symbol_counts[0xFF & prior_delta_symbol2]++;
              order_1_counts[0xFF & prior_delta_symbol2][0x80]++;
              symbol_counts[delta_symbol1 >> 8]++;
              order_1_counts[delta_symbol1 >> 8][0x80]++;
              symbol_counts[0xFF & delta_symbol1]++;
              order_1_counts[0xFF & delta_symbol1][0x80]++;
            }
            else if (i == num_in_char - 5) {
              prior_symbol1 = next_symbol1;
              prior_symbol2 = next_symbol2;
              prior_delta_symbol1 = delta_symbol1;
              prior_delta_symbol2 = delta_symbol2;
              next_symbol1 = in_char[i+4] << 8;
              delta_symbol1 = next_symbol1 - prior_symbol1 + 0x8080;
              symbol_counts[prior_delta_symbol1 >> 8]++;
              order_1_counts[prior_delta_symbol1 >> 8][delta_symbol1 >> 8]++;
              symbol_counts[0xFF & prior_delta_symbol1]++;
              order_1_counts[0xFF & prior_delta_symbol1][0x80]++;
              symbol_counts[prior_delta_symbol2 >> 8]++;
              order_1_counts[prior_delta_symbol2 >> 8][0x80]++;
              symbol_counts[0xFF & prior_delta_symbol2]++;
              order_1_counts[0xFF & prior_delta_symbol2][0x80]++;
              symbol_counts[delta_symbol1 >> 8]++;
              order_1_counts[delta_symbol1 >> 8][0x80]++;
            }
            else {
              prior_delta_symbol1 = delta_symbol1;
              prior_delta_symbol2 = delta_symbol2;
              symbol_counts[prior_delta_symbol1 >> 8]++;
              order_1_counts[prior_delta_symbol1 >> 8][0x80]++;
              symbol_counts[0xFF & prior_delta_symbol1]++;
              order_1_counts[0xFF & prior_delta_symbol1][0x80]++;
              symbol_counts[prior_delta_symbol2 >> 8]++;
              order_1_counts[prior_delta_symbol2 >> 8][0x80]++;
              symbol_counts[0xFF & prior_delta_symbol2]++;
              order_1_counts[0xFF & prior_delta_symbol2][0x80]++;
            }
            order_1_entropy = calculate_order_1_entropy(symbol_counts, order_1_counts);
            if (order_1_entropy < min_entropy) {
              fprintf(stderr,"Two channel big endian\n");
              fputc(0x58, fd_out);
              in_char_ptr = in_char + ((end_char_ptr - in_char - 6) & ~1);
              while (in_char_ptr >= in_char) {
                uint16_t delta_value = (*(in_char_ptr + 4) << 8) + *(in_char_ptr + 5)
                    - ((*in_char_ptr << 8) + *(in_char_ptr + 1)) + 0x80;
                *(in_char_ptr + 4) = delta_value >> 8;
                *(in_char_ptr + 5) = delta_value & 0xFF;
                in_char_ptr -= 2;
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
          else {
            // little endian
            uint16_t prior_symbol1 = (in_char[1] << 8) + in_char[0];
            uint16_t prior_symbol2 = (in_char[3] << 8) + in_char[2];
            uint16_t next_symbol1 = (in_char[5] << 8) + in_char[4];
            uint16_t next_symbol2 = (in_char[7] << 8) + in_char[6];
            uint16_t delta_symbol1 = next_symbol1 - prior_symbol1 + 0x8080;
            uint16_t delta_symbol2 = next_symbol2 - prior_symbol2 + 0x8080;
            uint16_t prior_delta_symbol1;
            uint16_t prior_delta_symbol2;
            symbol_counts[in_char[0]]++;
            order_1_counts[in_char[0]][delta_symbol1 >> 8]++;
            symbol_counts[in_char[1]]++;
            order_1_counts[in_char[1]][0xFF & delta_symbol1]++;
            symbol_counts[in_char[2]]++;
            order_1_counts[in_char[2]][delta_symbol2 >> 8]++;
            symbol_counts[in_char[3]]++;
            order_1_counts[in_char[3]][0xFF & delta_symbol2]++;
            for (i = 4 ; i < num_in_char - 7 ; i += 4) {
              prior_symbol1 = next_symbol1;
              prior_symbol2 = next_symbol2;
              prior_delta_symbol1 = delta_symbol1;
              prior_delta_symbol2 = delta_symbol2;
              next_symbol1 = (in_char[i+5] << 8) + in_char[i+4];
              next_symbol2 = (in_char[i+7] << 8) + in_char[i+6];
              delta_symbol1 = next_symbol1 - prior_symbol1 + 0x8080;
              delta_symbol2 = next_symbol2 - prior_symbol2 + 0x8080;
              symbol_counts[0xFF & prior_delta_symbol1]++;
              order_1_counts[0xFF & prior_delta_symbol1][0xFF & delta_symbol1]++;
              symbol_counts[prior_delta_symbol1 >> 8]++;
              order_1_counts[prior_delta_symbol1 >> 8][delta_symbol1 >> 8]++;
              symbol_counts[0xFF & prior_delta_symbol2]++;
              order_1_counts[0xFF & prior_delta_symbol2][0xFF & delta_symbol2]++;
              symbol_counts[prior_delta_symbol2 >> 8]++;
              order_1_counts[prior_delta_symbol2 >> 8][delta_symbol2 >> 8]++;
            }
            if (i == num_in_char - 7) {
              prior_symbol1 = next_symbol1;
              prior_symbol2 = next_symbol2;
              prior_delta_symbol1 = delta_symbol1;
              prior_delta_symbol2 = delta_symbol2;
              next_symbol1 = (in_char[i+5] << 8) + in_char[i+4];
              next_symbol2 = in_char[i+6];
              delta_symbol1 = next_symbol1 - prior_symbol1 + 0x8080;
              delta_symbol2 = next_symbol2 - prior_symbol2 + 0x8080;
              symbol_counts[0xFF & prior_delta_symbol1]++;
              order_1_counts[0xFF & prior_delta_symbol1][0xFF & delta_symbol1]++;
              symbol_counts[prior_delta_symbol1 >> 8]++;
              order_1_counts[prior_delta_symbol1 >> 8][delta_symbol1 >> 8]++;
              symbol_counts[0xFF & prior_delta_symbol2]++;
              order_1_counts[0xFF & prior_delta_symbol2][0xFF & delta_symbol1]++;
              symbol_counts[prior_delta_symbol2 >> 8]++;
              order_1_counts[prior_delta_symbol2 >> 8][0x80]++;
              symbol_counts[0xFF & delta_symbol1]++;
              order_1_counts[0xFF & delta_symbol1][0x80]++;
              symbol_counts[delta_symbol1 >> 8]++;
              order_1_counts[delta_symbol1 >> 8][0x80]++;
              symbol_counts[0xFF & delta_symbol2]++;
              order_1_counts[0xFF & delta_symbol2][0x80]++;
            }
            else if (i == num_in_char - 6) {
              prior_symbol1 = next_symbol1;
              prior_symbol2 = next_symbol2;
              prior_delta_symbol1 = delta_symbol1;
              prior_delta_symbol2 = delta_symbol2;
              next_symbol1 = (in_char[i+4] << 8) + in_char[i+5];
              delta_symbol1 = next_symbol1 - prior_symbol1 + 0x8080;
              symbol_counts[0xFF & prior_delta_symbol1]++;
              order_1_counts[0xFF & prior_delta_symbol1][0xFF & delta_symbol1]++;
              symbol_counts[prior_delta_symbol1 >> 8]++;
              order_1_counts[prior_delta_symbol1 >> 8][delta_symbol1 >> 8]++;
              symbol_counts[0xFF & prior_delta_symbol2]++;
              order_1_counts[0xFF & prior_delta_symbol2][0x80]++;
              symbol_counts[prior_delta_symbol2 >> 8]++;
              order_1_counts[prior_delta_symbol2 >> 8][0x80]++;
              symbol_counts[0xFF & delta_symbol1]++;
              order_1_counts[0xFF & delta_symbol1][0x80]++;
              symbol_counts[delta_symbol1 >> 8]++;
              order_1_counts[delta_symbol1 >> 8][0x80]++;
            }
            else if (i == num_in_char - 5) {
              prior_symbol1 = next_symbol1;
              prior_symbol2 = next_symbol2;
              prior_delta_symbol1 = delta_symbol1;
              prior_delta_symbol2 = delta_symbol2;
              next_symbol1 = in_char[i+4] << 8;
              delta_symbol1 = next_symbol1 - prior_symbol1 + 0x8080;
              symbol_counts[0xFF & prior_delta_symbol1]++;
              order_1_counts[0xFF & prior_delta_symbol1][0xFF & delta_symbol1]++;
              symbol_counts[prior_delta_symbol1 >> 8]++;
              order_1_counts[prior_delta_symbol1 >> 8][0x80]++;
              symbol_counts[0xFF & prior_delta_symbol2]++;
              order_1_counts[0xFF & prior_delta_symbol2][0x80]++;
              symbol_counts[prior_delta_symbol2 >> 8]++;
              order_1_counts[prior_delta_symbol2 >> 8][0x80]++;
              symbol_counts[delta_symbol1 >> 8]++;
              order_1_counts[delta_symbol1 >> 8][0x80]++;
            }
            else {
              prior_delta_symbol1 = delta_symbol1;
              prior_delta_symbol2 = delta_symbol2;
              symbol_counts[0xFF & prior_delta_symbol1]++;
              order_1_counts[0xFF & prior_delta_symbol1][0x80]++;
              symbol_counts[prior_delta_symbol1 >> 8]++;
              order_1_counts[prior_delta_symbol1 >> 8][0x80]++;
              symbol_counts[0xFF & prior_delta_symbol2]++;
              order_1_counts[0xFF & prior_delta_symbol2][0x80]++;
              symbol_counts[prior_delta_symbol2 >> 8]++;
              order_1_counts[prior_delta_symbol2 >> 8][0x80]++;
            }
            order_1_entropy = calculate_order_1_entropy(symbol_counts, order_1_counts);
            if (order_1_entropy < min_entropy) {
              fprintf(stderr,"Two channel little endian\n");
              fputc(0x78, fd_out);
              in_char_ptr = in_char + ((end_char_ptr - in_char - 6) & ~1);
              while (in_char_ptr >= in_char) {
                uint16_t delta_value = (*(in_char_ptr + 5) << 8) + *(in_char_ptr + 4)
                    - ((*(in_char_ptr + 1) << 8) + *in_char_ptr) + 0x80;
                *(in_char_ptr + 4) = delta_value & 0xFF;
                *(in_char_ptr + 5) = (delta_value >> 8) & 0xFF;
                in_char_ptr -= 2;
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
          // try big endian first
          clear_counts(symbol_counts, order_1_counts);
          uint32_t prior_symbol = (in_char[0] << 24) + (in_char[1] << 16) + (in_char[2] << 8) + in_char[3];
          uint32_t next_symbol = (in_char[4] << 24) + (in_char[5] << 16) + (in_char[6] << 8) + in_char[7];
          uint32_t delta_symbol = next_symbol - prior_symbol + 0x80808080;
          uint32_t prior_delta_symbol;
          symbol_counts[in_char[0]]++;
          order_1_counts[in_char[0]][0xFF & (delta_symbol >> 24)]++;
          symbol_counts[in_char[1]]++;
          order_1_counts[in_char[1]][0xFF & (delta_symbol >> 16)]++;
          symbol_counts[in_char[2]]++;
          order_1_counts[in_char[2]][0xFF & (delta_symbol >> 8)]++;
          symbol_counts[in_char[3]]++;
          order_1_counts[in_char[3]][0xFF & delta_symbol]++;
          for (i = 4 ; i < num_in_char - 7 ; i += 4) {
            prior_symbol = next_symbol;
            prior_delta_symbol = delta_symbol;
            next_symbol = (in_char[i+4] << 24) + (in_char[i+5] << 16) + (in_char[i+6] << 8) + in_char[i+7];
            delta_symbol = next_symbol - prior_symbol + 0x80808080;
            symbol_counts[prior_delta_symbol >> 24]++;
            order_1_counts[prior_delta_symbol >> 24][delta_symbol >> 24]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 16)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 16)][0xFF & (delta_symbol >> 16)]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 8)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 8)][0xFF & (delta_symbol >> 8)]++;
            symbol_counts[0xFF & prior_delta_symbol]++;
            order_1_counts[0xFF & prior_delta_symbol][0xFF & delta_symbol]++;
          }
          if (i == num_in_char - 7) {
            prior_symbol = next_symbol;
            prior_delta_symbol = delta_symbol;
            next_symbol = (in_char[i+4] << 24) + (in_char[i+5] << 16) + (in_char[i+6] << 8);
            delta_symbol = next_symbol - prior_symbol + 0x80808080;
            symbol_counts[prior_delta_symbol >> 24]++;
            order_1_counts[prior_delta_symbol >> 24][delta_symbol >> 24]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 16)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 16)][0xFF & (delta_symbol >> 16)]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 8)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 8)][0xFF & (delta_symbol >> 8)]++;
            symbol_counts[0xFF & prior_delta_symbol]++;
            order_1_counts[0xFF & prior_delta_symbol][0x80]++;
            symbol_counts[delta_symbol >> 24]++;
            order_1_counts[delta_symbol >> 24][0x80]++;
            symbol_counts[0xFF & (delta_symbol >> 16)]++;
            order_1_counts[0xFF & (delta_symbol >> 16)][0x80]++;
            symbol_counts[0xFF & (delta_symbol >> 8)]++;
            order_1_counts[0xFF & (delta_symbol >> 8)][0x80]++;
          }
          else if (i == num_in_char - 6) {
            prior_symbol = next_symbol;
            prior_delta_symbol = delta_symbol;
            next_symbol = (in_char[i+4] << 24) + (in_char[i+5] << 16);
            delta_symbol = next_symbol - prior_symbol + 0x80808080;
            symbol_counts[prior_delta_symbol >> 24]++;
            order_1_counts[prior_delta_symbol >> 24][delta_symbol >> 24]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 16)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 16)][0xFF & (delta_symbol >> 16)]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 8)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 8)][0x80]++;
            symbol_counts[0xFF & prior_delta_symbol]++;
            order_1_counts[0xFF & prior_delta_symbol][0x80]++;
            symbol_counts[delta_symbol >> 24]++;
            order_1_counts[delta_symbol >> 24][0x80]++;
            symbol_counts[0xFF & (delta_symbol >> 16)]++;
            order_1_counts[0xFF & (delta_symbol >> 16)][0x80]++;
          }
          else if (i == num_in_char - 5) {
            prior_symbol = next_symbol;
            prior_delta_symbol = delta_symbol;
            next_symbol = (in_char[i+4] << 24);
            delta_symbol = next_symbol - prior_symbol + 0x80808080;
            symbol_counts[prior_delta_symbol >> 24]++;
            order_1_counts[prior_delta_symbol >> 24][delta_symbol >> 24]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 16)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 16)][0x80]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 8)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 8)][0x80]++;
            symbol_counts[0xFF & prior_delta_symbol]++;
            order_1_counts[0xFF & prior_delta_symbol][0x80]++;
            symbol_counts[delta_symbol >> 24]++;
            order_1_counts[delta_symbol >> 24][0x80]++;
          }
          else {
            prior_delta_symbol = delta_symbol;
            symbol_counts[prior_delta_symbol >> 24]++;
            order_1_counts[prior_delta_symbol >> 24][0x80]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 16)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 16)][0x80]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 8)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 8)][0x80]++;
            symbol_counts[0xFF & prior_delta_symbol]++;
            order_1_counts[0xFF & prior_delta_symbol][0x80]++;
          }
          saved_entropy[0] = calculate_order_1_entropy(symbol_counts, order_1_counts);

          clear_counts(symbol_counts, order_1_counts);
          prior_symbol = (in_char[3] << 24) + (in_char[2] << 16) + (in_char[1] << 8) + in_char[0];
          next_symbol = (in_char[7] << 24) + (in_char[6] << 16) + (in_char[5] << 8) + in_char[4];
          delta_symbol = next_symbol - prior_symbol + 0x80808080;
          symbol_counts[in_char[0]]++;
          order_1_counts[in_char[0]][0xFF & delta_symbol]++;
          symbol_counts[in_char[1]]++;
          order_1_counts[in_char[1]][0xFF & (delta_symbol >> 8)]++;
          symbol_counts[in_char[2]]++;
          order_1_counts[in_char[2]][0xFF & (delta_symbol >> 16)]++;
          symbol_counts[in_char[3]]++;
          order_1_counts[in_char[3]][delta_symbol >> 24]++;
          for (i = 4 ; i < num_in_char - 7 ; i += 4) {
            prior_symbol = next_symbol;
            prior_delta_symbol = delta_symbol;
            next_symbol = (in_char[i+7] << 24) + (in_char[i+6] << 16) + (in_char[i+5] << 8) + in_char[i+4];
            delta_symbol = next_symbol - prior_symbol + 0x80808080;
            symbol_counts[0xFF & prior_delta_symbol]++;
            order_1_counts[0xFF & prior_delta_symbol][0xFF & delta_symbol]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 8)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 8)][0xFF & (delta_symbol >> 8)]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 16)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 16)][0xFF & (delta_symbol >> 16)]++;
            symbol_counts[prior_delta_symbol >> 24]++;
            order_1_counts[prior_delta_symbol >> 24][delta_symbol >> 24]++;
          }
          if (i == num_in_char - 7) {
            prior_symbol = next_symbol;
            prior_delta_symbol = delta_symbol;
            next_symbol = (in_char[i+6] << 16) + (in_char[i+5] << 8) + in_char[i+4];
            delta_symbol = next_symbol - prior_symbol + 0x80808080;
            symbol_counts[0xFF & prior_delta_symbol]++;
            order_1_counts[0xFF & prior_delta_symbol][0xFF & delta_symbol]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 8)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 8)][0xFF & (delta_symbol >> 8)]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 16)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 16)][0xFF & (delta_symbol >> 16)]++;
            symbol_counts[prior_delta_symbol >> 24]++;
            order_1_counts[prior_delta_symbol >> 24][0]++;
            symbol_counts[0xFF & delta_symbol]++;
            order_1_counts[0xFF & delta_symbol][0]++;
            symbol_counts[0xFF & (delta_symbol >> 8)]++;
            order_1_counts[0xFF & (delta_symbol >> 8)][0]++;
            symbol_counts[0xFF & (delta_symbol >> 16)]++;
            order_1_counts[0xFF & (delta_symbol >> 16)][0]++;
          }
          else if (i == num_in_char - 6) {
            prior_symbol = next_symbol;
            prior_delta_symbol = delta_symbol;
            next_symbol = (in_char[i+5] << 8) + in_char[i+4];
            delta_symbol = next_symbol - prior_symbol + 0x80808080;
            symbol_counts[0xFF & prior_delta_symbol]++;
            order_1_counts[0xFF & prior_delta_symbol][0xFF & delta_symbol]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 8)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 8)][0xFF & (delta_symbol >> 8)]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 16)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 16)][0]++;
            symbol_counts[prior_delta_symbol >> 24]++;
            order_1_counts[prior_delta_symbol >> 24][0]++;
            symbol_counts[0xFF & delta_symbol]++;
            order_1_counts[0xFF & delta_symbol][0]++;
            symbol_counts[0xFF & (delta_symbol >> 8)]++;
            order_1_counts[0xFF & (delta_symbol >> 8)][0]++;
          }
          else if (i == num_in_char - 5) {
            prior_symbol = next_symbol;
            prior_delta_symbol = delta_symbol;
            next_symbol = in_char[i+4];
            delta_symbol = next_symbol - prior_symbol + 0x80808080;
            symbol_counts[0xFF & prior_delta_symbol]++;
            order_1_counts[0xFF & prior_delta_symbol][0xFF & delta_symbol]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 8)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 8)][0]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 16)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 16)][0]++;
            symbol_counts[prior_delta_symbol >> 24]++;
            order_1_counts[prior_delta_symbol >> 24][0]++;
            symbol_counts[0xFF & delta_symbol]++;
            order_1_counts[0xFF & delta_symbol][0]++;
          }
          else {
            prior_delta_symbol = delta_symbol;
            symbol_counts[0xFF & prior_delta_symbol]++;
            order_1_counts[0xFF & prior_delta_symbol][0]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 8)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 8)][0]++;
            symbol_counts[0xFF & (prior_delta_symbol >> 16)]++;
            order_1_counts[0xFF & (prior_delta_symbol >> 16)][0]++;
            symbol_counts[prior_delta_symbol >> 24]++;
            order_1_counts[prior_delta_symbol >> 24][0]++;
          }
          order_1_entropy = calculate_order_1_entropy(symbol_counts, order_1_counts);

          if ((saved_entropy[0] < min_entropy) && (saved_entropy[0] < order_1_entropy)) {
            fprintf(stderr,"Big endian\n");
            fputc(0x18, fd_out);
            in_char_ptr = in_char + ((end_char_ptr - in_char - 8) & ~3);
            uint32_t value = (*(in_char_ptr + 4) << 24) + (*(in_char_ptr + 5) << 16)
                + (*(in_char_ptr + 6) << 8) + *(in_char_ptr + 7);
            while (in_char_ptr >= in_char) {
              uint32_t prior_value = (*in_char_ptr << 24) + (*(in_char_ptr + 1) << 16)
                  + (*(in_char_ptr + 2) << 8) + *(in_char_ptr + 3);
              uint32_t delta_value = value - prior_value + 0x808080;
              *(in_char_ptr + 4) = delta_value >> 24;
              *(in_char_ptr + 5) = (delta_value >> 16) & 0xFF;
              *(in_char_ptr + 6) = (delta_value >> 8) & 0xFF;
              *(in_char_ptr + 7) = delta_value & 0xFF;
              value = prior_value;
              in_char_ptr -= 4;
            }
          }
          else if (order_1_entropy < min_entropy) {
            fprintf(stderr,"Little endian\n");
            fputc(0x38, fd_out);
            in_char_ptr = in_char + ((end_char_ptr - in_char - 8) & ~3);
            uint32_t value = (*(in_char_ptr + 7) << 24) + (*(in_char_ptr + 6) << 16)
                + (*(in_char_ptr + 5) << 8) + *(in_char_ptr + 4);
            while (in_char_ptr >= in_char) {
              uint32_t prior_value = (*(in_char_ptr + 3) << 24) + (*(in_char_ptr + 2) << 16)
                  + (*(in_char_ptr + 1) << 8) + *in_char_ptr;
              uint32_t delta_value = value - prior_value + 0x808080;
              *(in_char_ptr + 7) = delta_value >> 24;
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
    else if (stride == 3) {
      fputc(6, fd_out);
      in_char_ptr = end_char_ptr - 3;
      while (--in_char_ptr >= in_char)
        *(in_char_ptr + 3) -= *in_char_ptr;
    }
    else {
      fputc(0x80 + stride, fd_out);
      in_char_ptr = end_char_ptr - stride;
      while (--in_char_ptr >= in_char)
        *(in_char_ptr + stride) -= *in_char_ptr;
      in_char_ptr = in_char + stride - 1;
      while (--in_char_ptr >= in_char)
        *(in_char_ptr + 1) -= *in_char_ptr;
    }

    if ((stride == 2) || (stride == 4)) {
      uint8_t * in_char2 = (uint8_t *)malloc(CHARS_TO_WRITE); // SHOULD FREE!!
      uint8_t * in_char2_ptr;
      uint8_t * start_block_ptr = in_char;
      uint8_t * end_block_ptr = start_block_ptr + CHARS_TO_WRITE;
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