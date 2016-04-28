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
//
// Usage:
//   GLZAformat <infilename> <outfilename>


#include <stdio.h>
#include <stdlib.h>
#include <time.h>

const CAP_CHAR = 0x43;

unsigned char in_char[1050000000];
const CHARS_TO_WRITE = 4000000;
unsigned char out_char_buffer[4000100];

int main(int argc, char* argv[])
{
  FILE *fd_in, *fd_out;

  unsigned int num_in_char, num_out_char;
  unsigned char *in_char_ptr, *end_char_ptr, *out_char_ptr, this_char, prev_char, next_char;
  unsigned int num_AZ, num_az_pre_AZ, num_az_post_AZ;
  unsigned long long int start_time;


  start_time = clock();

  if ((fd_in = fopen(argv[1],"rb"))==NULL)
  {
    printf("fopen error - fd_in\n");
    exit(0);
  }
  if ((fd_out = fopen(argv[2],"wb"))==NULL)
  {
    printf("fopen error - fd_out\n");
    exit(0);
  }

  /* read the file into local memory */
  fseek(fd_in, 0, SEEK_END);
  num_in_char = ftell(fd_in);
  rewind(fd_in);
  num_in_char = fread(in_char, 1, num_in_char, fd_in);
  fclose(fd_in);

  end_char_ptr = in_char + num_in_char;
  num_AZ = 0;
  num_az_pre_AZ = 0;
  num_az_post_AZ = 0;

  if (num_in_char > 1)
  {
    in_char_ptr = in_char;
    this_char = *in_char_ptr++;
    prev_char = this_char;
    if ((this_char >= 'A') && (this_char <= 'Z'))
    {
      num_AZ++;
      next_char = *in_char_ptr;
      if ((next_char >= 'a') && (next_char <= 'z'))
        num_az_post_AZ++;
    }
    while (in_char_ptr != end_char_ptr - 1)
    {
      this_char = *in_char_ptr++;
      if ((this_char >= 'A') && (this_char <= 'Z'))
      {
        num_AZ++;
        next_char = *in_char_ptr;
        if ((next_char >= 'a') && (next_char <= 'z'))
          num_az_post_AZ++;
        if ((prev_char >= 'a') && (prev_char <= 'z'))
          num_az_pre_AZ++;
      }
      prev_char = this_char;
    }
    if ((this_char >= 'A') && (this_char <= 'Z'))
    {
      num_AZ++;
      next_char = *in_char_ptr;
      if ((prev_char >= 'a') && (prev_char <= 'z'))
        num_az_pre_AZ++;
    }
  }

  in_char_ptr = in_char;
  out_char_ptr = out_char_buffer;
  num_out_char = 0;

  if ((num_AZ > (num_in_char >> 10)) && (2 * num_az_post_AZ > num_AZ) && (num_az_post_AZ > 10 * num_az_pre_AZ))
  {
    printf("Pre and capital encoding %u bytes\n",num_in_char);
    fputc(1,fd_out);
    while (in_char_ptr != end_char_ptr)
    {
      if (((int)*in_char_ptr >= (int)'A') && ((int)*in_char_ptr <= (int)'Z'))
      {
        *out_char_ptr++ = CAP_CHAR;
        *out_char_ptr++ = *in_char_ptr++ + ('a' - 'A');
      }
      else if (*in_char_ptr >= 0xFE)
      {
        *out_char_ptr++ = *in_char_ptr++;
        *out_char_ptr++ = 0xFF;
      }
      else
        *out_char_ptr++ = *in_char_ptr++;

      if (out_char_ptr - out_char_buffer > CHARS_TO_WRITE)
      {
        fwrite(out_char_buffer, 1, out_char_ptr - out_char_buffer, fd_out);
        num_out_char += out_char_ptr - out_char_buffer;
        out_char_ptr = out_char_buffer;
        fflush(fd_out);
      }
    }
  }
  else
  {
    printf("Pre encoding %u bytes\n",num_in_char);
    fputc(0,fd_out);
    while (in_char_ptr != end_char_ptr)
    {
      if (*in_char_ptr >= 0xFE)
      {
        *out_char_ptr++ = *in_char_ptr++;
        *out_char_ptr++ = 0xFF;
      }
      else
        *out_char_ptr++ = *in_char_ptr++;

      if (out_char_ptr - out_char_buffer > CHARS_TO_WRITE)
      {
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
