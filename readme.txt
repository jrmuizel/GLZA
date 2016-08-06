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

GLZA is an experimental grammar compression toolset.  Compression is accomoplished by using GLZAformat, GLZAcompress
  and GLZAdecode, in that order.  Decompression is accomplished by using GLZAdecode.  In general, GLZA is slow to
  compress but for text-like files, achieves Pareto Frontier decompression speeds vs. compression ratio with low
  decompression RAM use.
GLZAformat is a preprocessor that detects the data type, performs capital encoding on textual files and
  performs 1, 2 or 4 byte delta filtering on certain strided files.
GLZAcompress performs a grammar transformation by recursively finding sets of production rules until no new
  profitable production rules can be found.  This step may be skipped, in which case GLZA is effectively an
  order-1 compressor.
GLZAencode encodes the grammar using a variation of the Grammatical Ziv-Lempel format.
GLZAdecode decodes the data.

Usage:
   GLZAformat [-c#] [-d#] [-l#] <infilename> <outfilename>
     where
       -c0 disables capital encoding
       -c1 forces text processing and capital encoding
       -d0 disables delta encoding
       -l0 disables capital lock encoding

   GLZAcompress [-m#] [-p#] [-r#] [-w0] <infilename> <outfilename>
     where
       -m# sets the production cost, default 6.0
       -p# sets the profit ratio weighting power, default 2.0 for capital encoded or UTF8 compliant files, 0.5 otherwise
           (0.0 is approximately most compressive bitwise, ie. maximizing the order 0 profit of new productions)
       -r# sets the approximate RAM usage in millions of bytes
       -w0 disables the first cycle word only search

   GLZAencode [-m#] [-v#] <infilename> <outfilename>
     where
       -m# overrides the programs decision on whether to use mtf.  -m0 disables mtf, -m1 enables mtf
       -v0 prints the dictionary to stdout, most frequent first
       -v1 prints the dicitonary to stdout, simple symbols followed by complex symbols in the order they were created

   GLZAdecode [-t#] <infilename> <outfilename>
     where
       -t# sets the number of threads (1 or 2)

For more details on GLZA and the GLZ format, see http://encode.ru/threads/2427-GLZA.