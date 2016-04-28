/***********************************************************************

Copyright 2015 Kennon Conrad

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

enum { TOP = 1 << 24, BUF_SIZE = 0x80000 };
enum { UP_FREQ_SYM_TYPE = 1, FREQ_SYM_TYPE_BOT = 0x40 };
enum { UP_FREQ_MTF_QUEUE_NUM2 = 4, UP_FREQ_MTF_QUEUE_NUM = 10, FREQ_MTF_QUEUE_NUM_BOT = 0x100 };
enum { UP_FREQ_MTF_QUEUE_POS = 5, FREQ_MTF_QUEUE_POS_BOT = 0x4000 };
enum { UP_FREQ_MTFG_QUEUE_POS = 2, FREQ_MTFG_QUEUE_POS_BOT = 0x4000 };
enum { UP_FREQ_SID = 3, FREQ_SID_BOT = 0x1000 };
enum { UP_FREQ_INST = 8, FREQ_INST_BOT = 0x8000 };
enum { UP_FREQ_ERG = 1, FREQ_ERG_BOT = 0x20 };
enum { UP_FREQ_WORD_TAG = 1, FREQ_WORD_TAG_BOT = 0x80 };
enum { UP_FREQ_FIRST_CHAR = 8, FREQ_FIRST_CHAR_BOT = 0x2000 };
enum { NOT_CAP = 0, CAP = 1 };
enum { LEVEL0 = 0, LEVEL1 = 1, LEVEL0_CAP = 2, LEVEL1_CAP = 3 };

unsigned int NumInChar, InCharNum, OutCharNum;
unsigned int RangeLow, RangeHigh, count, BaseSymbol, SymbolIndex, BinCode, FirstChar;
unsigned int low, code, range;
unsigned char InBuffer[BUF_SIZE], OutBuffer0[BUF_SIZE], OutBuffer1[BUF_SIZE], OutBufferNum, *OutBuffer;
unsigned char Symbol, SIDSymbol, FoundIndex, mtfg_queue_position, mtf_queue_number, Instances, CodeLength;
unsigned char SymbolFirstChar[4][0x100][0x100];
unsigned char RangeScaleSymType[4], RangeScaleERG[3], RangeScaleWordTag;
unsigned char FreqSymType[4][4], FreqERG[3], FreqWordTag;
unsigned short int RangeScaleMtfQueueNum[2], RangeScaleMtfQueuePos[2][14], RangeScaleMtfgQueuePos[2];
unsigned short int RangeScaleSID[2], RangeScaleINST[2][16];
unsigned short int RangeScaleFirstChar[4][0x100];
unsigned short int RangeScaleFirstCharSection[0x100][7];
unsigned short int FreqMtfQueueNum[2][14], FreqMtfQueuePos[2][14][64], FreqMtfgQueuePos[2][256];
unsigned short int FreqSID[2][16], FreqINST[2][16][38], FreqFirstChar[4][0x100][0x100], FreqFirstCharBinary[0x100][0x100];
unsigned short int DictionaryBins, BinNum;
FILE * InFile, * OutFile;


#define StartModelSymType() {               \
  char i = 3;                               \
  do {                                      \
    FreqSymType[i][0] = 1;                  \
    FreqSymType[i][1] = 5;                  \
    if (use_mtf) {                          \
      FreqSymType[i][3] = 1;                \
      if (max_regular_code_length >= 11) {  \
        FreqSymType[i][2] = 1;              \
        RangeScaleSymType[i] = 8;           \
      }                                     \
      else {                                \
        FreqSymType[i][2] = 0;              \
        RangeScaleSymType[i] = 7;           \
      }                                     \
    }                                       \
    else {                                  \
      FreqSymType[i][2] = 0;                \
      FreqSymType[i][3] = 0;                \
      RangeScaleSymType[i] = 6;             \
    }                                       \
  } while (i--);                            \
}
#define StartModelMtfQueueNum() {    \
  unsigned char i = 1;               \
  do {                               \
    unsigned char j = 13;            \
    do {                             \
      FreqMtfQueueNum[i][j] = 8;     \
    } while (j--);                   \
    RangeScaleMtfQueueNum[i] = 112;  \
  } while (i--);                     \
}
#define StartModelMtfQueuePos() {        \
  unsigned char i = 1;                   \
  do {                                   \
    unsigned char j = 13;                \
    do {                                 \
      unsigned char k = 63;              \
      do {                               \
        FreqMtfQueuePos[i][j][k] = 1;    \
      } while (k--);                     \
      RangeScaleMtfQueuePos[i][j] = 64;  \
    } while (j--);                       \
  } while (i--);                         \
}
#define StartModelMtfgQueuePos() {                \
  unsigned char i = 1;                            \
  do {                                            \
    unsigned char j = 0;                          \
    do {                                          \
      FreqMtfgQueuePos[i][j] = 128;               \
    } while (++j != 5);                           \
    do {                                          \
      FreqMtfgQueuePos[i][j] = 64;                \
    } while (++j != 8);                           \
    do {                                          \
      FreqMtfgQueuePos[i][j] = 32;                \
    } while (++j != 16);                          \
    if (max_regular_code_length > 11) {           \
      do {                                        \
        FreqMtfgQueuePos[i][j] = 16;              \
      } while (++j != 32);                        \
      if (max_regular_code_length > 12) {         \
        do {                                      \
          FreqMtfgQueuePos[i][j] = 8;             \
        } while (++j != 64);                      \
        if (max_regular_code_length > 13) {       \
          do {                                    \
            FreqMtfgQueuePos[i][j] = 4;           \
          } while (++j != 128);                   \
          if (max_regular_code_length > 14) {     \
            do {                                  \
              FreqMtfgQueuePos[i][j] = 2;         \
            } while (++j != 192);                 \
            if (max_regular_code_length > 15) {   \
              do {                                \
                FreqMtfgQueuePos[i][j] = 1;       \
              } while (++j);                      \
              RangeScaleMtfgQueuePos[i] = 0x800;  \
            }                                     \
            else                                  \
              RangeScaleMtfgQueuePos[i] = 0x7C0;  \
          }                                       \
          else                                    \
            RangeScaleMtfgQueuePos[i] = 0x740;    \
        }                                         \
        else                                      \
          RangeScaleMtfgQueuePos[i] = 0x640;      \
      }                                           \
      else                                        \
        RangeScaleMtfgQueuePos[i] = 0x540;        \
    }                                             \
    else                                          \
      RangeScaleMtfgQueuePos[i] = 0x440;          \
    while (j)                                     \
      FreqMtfgQueuePos[i][j++] = 0;               \
  } while (i--);                                  \
}
#define StartModelSID() {   \
  unsigned char i = 1;      \
  do {                      \
    unsigned char j = 15;   \
    do {                    \
      FreqSID[i][j] = 1;    \
    } while (j--);          \
    RangeScaleSID[i] = 16;  \
  } while (i--);            \
}
#define StartModelINST(num_inst_codes) {      \
  unsigned char i = 1;                        \
  do {                                        \
    unsigned char j = 15;                     \
    do {                                      \
      unsigned char k = num_inst_codes - 1;   \
      do {                                    \
        FreqINST[i][j][k] = 1;                \
      } while (k--);                          \
      RangeScaleINST[i][j] = num_inst_codes;  \
    } while (j--);                            \
  } while (i--);                              \
}
#define StartModelERG() {  \
  FreqERG[0] = 1;          \
  RangeScaleERG[0] = 2;    \
  FreqERG[1] = 1;          \
  RangeScaleERG[1] = 2;    \
  FreqERG[2] = 1;          \
  RangeScaleERG[2] = 2;    \
}
#define StartModelWordTag() {  \
  FreqWordTag = 1;             \
  RangeScaleWordTag = 2;       \
}
#define StartModelFirstChar() {            \
  unsigned char i = 0xFF;                  \
  do {                                     \
    unsigned char j = 0xFF;                \
    do {                                   \
      FreqFirstChar[0][i][j] = 0;          \
      FreqFirstChar[1][i][j] = 0;          \
      FreqFirstChar[2][i][j] = 0;          \
      FreqFirstChar[3][i][j] = 0;          \
    } while (j--);                         \
    RangeScaleFirstChar[0][i] = 0;         \
    RangeScaleFirstChar[1][i] = 0;         \
    RangeScaleFirstChar[2][i] = 0;         \
    RangeScaleFirstChar[3][i] = 0;         \
  } while (i--);                           \
}
#define StartModelFirstCharBinary() {      \
  unsigned char i = 0xFF;                  \
  do {                                     \
    unsigned char j = 0xFF;                \
    do {                                   \
      FreqFirstCharBinary[i][j] = 0;       \
    } while (j--);                         \
    RangeScaleFirstChar[0][i] = 0;         \
    RangeScaleFirstCharSection[i][0] = 0;  \
    RangeScaleFirstCharSection[i][1] = 0;  \
    RangeScaleFirstCharSection[i][2] = 0;  \
    RangeScaleFirstCharSection[i][3] = 0;  \
    RangeScaleFirstCharSection[i][4] = 0;  \
    RangeScaleFirstCharSection[i][5] = 0;  \
    RangeScaleFirstCharSection[i][6] = 0;  \
  } while (i--);                           \
}
#define rescaleSymType(Context) {                                                              \
  RangeScaleSymType[Context] = FreqSymType[Context][0] = (FreqSymType[Context][0] + 1) >> 1;   \
  RangeScaleSymType[Context] += FreqSymType[Context][1] = (FreqSymType[Context][1] + 1) >> 1;  \
  RangeScaleSymType[Context] += FreqSymType[Context][2] = (FreqSymType[Context][2] + 1) >> 1;  \
  RangeScaleSymType[Context] += FreqSymType[Context][3] = (FreqSymType[Context][3] + 1) >> 1;  \
}
#define rescaleMtfQueueNum(Context) {                                                                       \
  unsigned char i = 12;                                                                                     \
  RangeScaleMtfQueueNum[Context] = FreqMtfQueueNum[Context][13] -= (FreqMtfQueueNum[Context][13] >> 2);     \
  do {                                                                                                      \
    RangeScaleMtfQueueNum[Context] += (FreqMtfQueueNum[Context][i] -= (FreqMtfQueueNum[Context][i] >> 2));  \
  } while (i--);                                                                                            \
}
#define rescaleMtfQueuePos(Context, mtf_queue_number) {                                                \
  unsigned char i = 62;                                                                                \
  RangeScaleMtfQueuePos[Context][mtf_queue_number] = (FreqMtfQueuePos[Context][mtf_queue_number][63]   \
      = (FreqMtfQueuePos[Context][mtf_queue_number][63] + 1) >> 1);                                    \
  do {                                                                                                 \
    RangeScaleMtfQueuePos[Context][mtf_queue_number] += FreqMtfQueuePos[Context][mtf_queue_number][i]  \
        = (FreqMtfQueuePos[Context][mtf_queue_number][i] + 1) >> 1;                                    \
  } while (i--);                                                                                       \
}
#define rescaleMtfQueuePosQ0(Context) {                                  \
  unsigned char i = 62;                                                  \
  RangeScaleMtfQueuePos[Context][0] = (FreqMtfQueuePos[Context][0][63]   \
      = (FreqMtfQueuePos[Context][0][63] + 1) >> 1);                     \
  do {                                                                   \
    RangeScaleMtfQueuePos[Context][0] += FreqMtfQueuePos[Context][0][i]  \
        = (FreqMtfQueuePos[Context][0][i] + 1) >> 1;                     \
  } while (i--);                                                         \
}
#define rescaleMtfgQueuePos(Context) {                                                                          \
  unsigned char i = 1;                                                                                          \
  RangeScaleMtfgQueuePos[Context] = FreqMtfgQueuePos[Context][0] = (FreqMtfgQueuePos[Context][0] + 1) >> 1;     \
  do {                                                                                                          \
    RangeScaleMtfgQueuePos[Context] += FreqMtfgQueuePos[Context][i] = (FreqMtfgQueuePos[Context][i] + 1) >> 1;  \
  } while (++i);                                                                                                \
}
#define rescaleSID(Context) {                                                        \
  unsigned char i = 14;                                                              \
  RangeScaleSID[Context] = FreqSID[Context][15] = (FreqSID[Context][15] + 1) >> 1;   \
  do {                                                                               \
    RangeScaleSID[Context] += FreqSID[Context][i] = (FreqSID[Context][i] + 1) >> 1;  \
  } while (i--);                                                                     \
}
#define rescaleINST(Context) {                                                                                           \
  unsigned char i = 34;                                                                                                  \
  RangeScaleINST[Context][SIDSymbol] = (FreqINST[Context][SIDSymbol][35] = (FreqINST[Context][SIDSymbol][35] + 1) >> 1); \
  do {                                                                                                                   \
    RangeScaleINST[Context][SIDSymbol] += FreqINST[Context][SIDSymbol][i] = (FreqINST[Context][SIDSymbol][i] + 1) >> 1;  \
  } while (i--);                                                                                                         \
}
#define rescaleINST1(Context) {                                                                   \
  unsigned char i = 34;                                                                           \
  RangeScaleINST[Context][0] = (FreqINST[Context][0][35] = (FreqINST[Context][0][35] + 1) >> 1);  \
  do {                                                                                            \
    RangeScaleINST[Context][0] += FreqINST[Context][0][i] = (FreqINST[Context][0][i] + 1) >> 1;   \
  } while (i--);                                                                                  \
}
#define rescaleERG(Context) {                        \
  RangeScaleERG[Context] = (FREQ_ERG_BOT >> 1) + 1;  \
  FreqERG[Context] = (FreqERG[Context] + 1) >> 1;    \
}
#define rescaleWordTag() {                           \
  RangeScaleWordTag = (FREQ_WORD_TAG_BOT >> 1) + 1;  \
  FreqWordTag = (FreqWordTag + 1) >> 1;              \
}
#define rescaleFirstChar(SymType, Context) {                                     \
  unsigned char i = 0xFE;                                                        \
  RangeScaleFirstChar[SymType][Context] = FreqFirstChar[SymType][Context][0xFF]  \
      = (FreqFirstChar[SymType][Context][0xFF] + 1) >> 1;                        \
  do {                                                                           \
    RangeScaleFirstChar[SymType][Context] += FreqFirstChar[SymType][Context][i]  \
        = (FreqFirstChar[SymType][Context][i] + 1) >> 1;                         \
  } while (i--);                                                                 \
}
#define rescaleFirstCharBinary(Context) {                                                                             \
  RangeScaleFirstChar[0][Context] = FreqFirstCharBinary[Context][0] = (FreqFirstCharBinary[Context][0] + 1) >> 1;     \
  unsigned char i = 1;                                                                                                \
  do {                                                                                                                \
    RangeScaleFirstChar[0][Context] += FreqFirstCharBinary[Context][i] = (FreqFirstCharBinary[Context][i] + 1) >> 1;  \
  } while (++i != 0x20);                                                                                              \
  RangeScaleFirstCharSection[Context][0] = RangeScaleFirstChar[0][Context];                                           \
  do {                                                                                                                \
    RangeScaleFirstChar[0][Context] += FreqFirstCharBinary[Context][i] = (FreqFirstCharBinary[Context][i] + 1) >> 1;  \
  } while (++i != 0x40);                                                                                              \
  RangeScaleFirstCharSection[Context][1] = RangeScaleFirstChar[0][Context];                                           \
  do {                                                                                                                \
    RangeScaleFirstChar[0][Context] += FreqFirstCharBinary[Context][i] = (FreqFirstCharBinary[Context][i] + 1) >> 1;  \
  } while (++i != 0x60);                                                                                              \
  RangeScaleFirstCharSection[Context][2] = RangeScaleFirstChar[0][Context] - RangeScaleFirstCharSection[Context][1];  \
  do {                                                                                                                \
    RangeScaleFirstChar[0][Context] += FreqFirstCharBinary[Context][i] = (FreqFirstCharBinary[Context][i] + 1) >> 1;  \
  } while (++i != 0x80);                                                                                              \
  RangeScaleFirstCharSection[Context][3] = RangeScaleFirstChar[0][Context];                                           \
  do {                                                                                                                \
    RangeScaleFirstChar[0][Context] += FreqFirstCharBinary[Context][i] = (FreqFirstCharBinary[Context][i] + 1) >> 1;  \
  } while (++i != 0xA0);                                                                                              \
  RangeScaleFirstCharSection[Context][4] = RangeScaleFirstChar[0][Context] - RangeScaleFirstCharSection[Context][3];  \
  do {                                                                                                                \
    RangeScaleFirstChar[0][Context] += FreqFirstCharBinary[Context][i] = (FreqFirstCharBinary[Context][i] + 1) >> 1;  \
  } while (++i != 0xC0);                                                                                              \
  RangeScaleFirstCharSection[Context][5] = RangeScaleFirstChar[0][Context] - RangeScaleFirstCharSection[Context][3];  \
  do {                                                                                                                \
    RangeScaleFirstChar[0][Context] += FreqFirstCharBinary[Context][i] = (FreqFirstCharBinary[Context][i] + 1) >> 1;  \
  } while (++i != 0xE0);                                                                                              \
  RangeScaleFirstCharSection[Context][6] = RangeScaleFirstChar[0][Context] - RangeScaleFirstCharSection[Context][5]   \
      - RangeScaleFirstCharSection[Context][3];                                                                       \
  do {                                                                                                                \
    RangeScaleFirstChar[0][Context] += FreqFirstCharBinary[Context][i] = (FreqFirstCharBinary[Context][i] + 1) >> 1;  \
  } while (++i);                                                                                                      \
}
#define UpFreqMtfQueueNum(Context) {                                                        \
  FreqMtfQueueNum[Context][mtf_queue_number] += UP_FREQ_MTF_QUEUE_NUM2;                     \
  if ((RangeScaleMtfQueueNum[Context] += UP_FREQ_MTF_QUEUE_NUM2) > FREQ_MTF_QUEUE_NUM_BOT)  \
    rescaleMtfQueueNum(Context);                                                            \
}
#define UpFreqMtfQueueNumD(Context) {                                                       \
  FreqMtfQueueNum[Context][mtf_queue_number] += UP_FREQ_MTF_QUEUE_NUM2;                     \
  if ((RangeScaleMtfQueueNum[Context] += UP_FREQ_MTF_QUEUE_NUM2) > FREQ_MTF_QUEUE_NUM_BOT)  \
    rescaleMtfQueueNum(Context);                                                            \
}
#define UpFreqMtfQueueNumHitD(Context) {                                                    \
  FreqMtfQueueNum[Context][mtf_queue_number] += UP_FREQ_MTF_QUEUE_NUM;                      \
  if ((RangeScaleMtfQueueNum[Context] += UP_FREQ_MTF_QUEUE_NUM) > FREQ_MTF_QUEUE_NUM_BOT)   \
    rescaleMtfQueueNum(Context);                                                            \
}
#ifdef encode
#define WriteByte(Value, File) {                                      \
  OutBuffer[OutCharNum++] = (unsigned char)(Value);                   \
  if (OutCharNum == BUF_SIZE) {                                       \
    fflush(File);                                                     \
    fwrite(OutBuffer,1,BUF_SIZE,File);                                \
    OutBuffer = (OutBuffer == OutBuffer0) ? OutBuffer1 : OutBuffer0;  \
    OutCharNum = 0;                                                   \
  }                                                                   \
}
#define NormalizeEncoder(bot) {                                                                \
  while ((low ^ (low + range)) < TOP || range < (bot) && ((range = -low & ((bot) - 1)), 1)) {  \
    WriteByte(low >> 24, OutFile);                                                             \
    range <<= 8;                                                                               \
    low <<= 8;                                                                                 \
  }                                                                                            \
}
#define EncodeDictType(Context) {                                                                      \
  NormalizeEncoder(FREQ_SYM_TYPE_BOT);                                                                 \
  range = FreqSymType[Context][0] * (range / RangeScaleSymType[Context]);                              \
  FreqSymType[Context][0] += UP_FREQ_SYM_TYPE;                                                         \
  if ((RangeScaleSymType[Context] += UP_FREQ_SYM_TYPE) > FREQ_SYM_TYPE_BOT)                            \
    rescaleSymType(Context);                                                                           \
}
#define EncodeNewType(Context) {                                                                       \
  NormalizeEncoder(FREQ_SYM_TYPE_BOT);                                                                 \
  low += FreqSymType[Context][0] * (range /= RangeScaleSymType[Context]);                              \
  range *= FreqSymType[Context][1];                                                                    \
  FreqSymType[Context][1] += UP_FREQ_SYM_TYPE;                                                         \
  if ((RangeScaleSymType[Context] += UP_FREQ_SYM_TYPE) > FREQ_SYM_TYPE_BOT)                            \
    rescaleSymType(Context);                                                                           \
}
#define EncodeMtfgType(Context) {                                                                      \
  NormalizeEncoder(FREQ_SYM_TYPE_BOT);                                                                 \
  low += (FreqSymType[Context][0] + FreqSymType[Context][1]) * (range /= RangeScaleSymType[Context]);  \
  range *= FreqSymType[Context][2];                                                                    \
  FreqSymType[Context][2] += UP_FREQ_SYM_TYPE;                                                         \
  if ((RangeScaleSymType[Context] += UP_FREQ_SYM_TYPE) > FREQ_SYM_TYPE_BOT)                            \
    rescaleSymType(Context);                                                                           \
}
#define EncodeMtfType(Context) {                                                                       \
  NormalizeEncoder(FREQ_SYM_TYPE_BOT);                                                                 \
  low += (FreqSymType[Context][0] + FreqSymType[Context][1] + FreqSymType[Context][2])                 \
      * (range /= RangeScaleSymType[Context]);                                                         \
  range *= FreqSymType[Context][3];                                                                    \
  FreqSymType[Context][3] += UP_FREQ_SYM_TYPE;                                                         \
  if ((RangeScaleSymType[Context] += UP_FREQ_SYM_TYPE) > FREQ_SYM_TYPE_BOT)                            \
    rescaleSymType(Context);                                                                           \
}
#define EncodeMtfQueueNum(Context) {                                                       \
  NormalizeEncoder(FREQ_MTF_QUEUE_NUM_BOT);                                                \
  if (mtf_queue_number == 0) {                                                             \
    range = FreqMtfQueueNum[Context][0] * (range / RangeScaleMtfQueueNum[Context]);        \
    FreqMtfQueueNum[Context][0] += UP_FREQ_MTF_QUEUE_NUM;                                  \
  }                                                                                        \
  else {                                                                                   \
    RangeLow = FreqMtfQueueNum[Context][0];                                                \
    FoundIndex = 1;                                                                        \
    while (FoundIndex != mtf_queue_number)                                                 \
      RangeLow += FreqMtfQueueNum[Context][FoundIndex++];                                  \
    low += RangeLow * (range /= RangeScaleMtfQueueNum[Context]);                           \
    range *= FreqMtfQueueNum[Context][FoundIndex];                                         \
    FreqMtfQueueNum[Context][FoundIndex] += UP_FREQ_MTF_QUEUE_NUM;                         \
  }                                                                                        \
  if ((RangeScaleMtfQueueNum[Context] += UP_FREQ_MTF_QUEUE_NUM) > FREQ_MTF_QUEUE_NUM_BOT)  \
    rescaleMtfQueueNum(Context);                                                           \
}
#define EncodeMtfQueueNumLastSymbol(Context) {                                             \
  NormalizeEncoder(FREQ_MTF_QUEUE_NUM_BOT);                                                \
  if (mtf_queue_number == 0)                                                               \
    range = FreqMtfQueueNum[Context][0] * (range / RangeScaleMtfQueueNum[Context]);        \
  else {                                                                                   \
    RangeLow = FreqMtfQueueNum[Context][0];                                                \
    FoundIndex = 1;                                                                        \
    while (FoundIndex != mtf_queue_number)                                                 \
      RangeLow += FreqMtfQueueNum[Context][FoundIndex++];                                  \
    low += RangeLow * (range /= RangeScaleMtfQueueNum[Context]);                           \
    range *= FreqMtfQueueNum[Context][FoundIndex];                                         \
  }                                                                                        \
}
#define EncodeMtfQueuePos(Context) {                                                                         \
  NormalizeEncoder(FREQ_MTF_QUEUE_POS_BOT);                                                                  \
  unsigned short int RangeScale = RangeScaleMtfQueuePos[Context][mtf_queue_number];                          \
  if (mtf_queue_size[mtf_queue_number+2] != MTF_QUEUE_SIZE) {                                                \
    unsigned char tqp = MTF_QUEUE_SIZE - 1;                                                                  \
    do {                                                                                                     \
      RangeScale -= FreqMtfQueuePos[Context][mtf_queue_number][tqp];                                         \
    } while (tqp-- != mtf_queue_size[mtf_queue_number+2]);                                                   \
  }                                                                                                          \
  if (mtf_queue_position == 0) {                                                                             \
    range = FreqMtfQueuePos[Context][mtf_queue_number][0] * (range / RangeScale);                            \
    FreqMtfQueuePos[Context][mtf_queue_number][0] += UP_FREQ_MTF_QUEUE_POS;                                  \
  }                                                                                                          \
  else {                                                                                                     \
    RangeLow = FreqMtfQueuePos[Context][mtf_queue_number][0];                                                \
    FoundIndex = 1;                                                                                          \
    while (FoundIndex != mtf_queue_position)                                                                 \
      RangeLow += FreqMtfQueuePos[Context][mtf_queue_number][FoundIndex++];                                  \
    low += RangeLow * (range /= RangeScale);                                                                 \
    range *= FreqMtfQueuePos[Context][mtf_queue_number][FoundIndex];                                         \
    FreqMtfQueuePos[Context][mtf_queue_number][FoundIndex] += UP_FREQ_MTF_QUEUE_POS;                         \
  }                                                                                                          \
  if ((RangeScaleMtfQueuePos[Context][mtf_queue_number] += UP_FREQ_MTF_QUEUE_POS) > FREQ_MTF_QUEUE_POS_BOT)  \
    rescaleMtfQueuePos(Context, mtf_queue_number);                                                           \
}
#define EncodeMtfgQueuePos(Context) {                                                         \
  NormalizeEncoder(FREQ_MTFG_QUEUE_POS_BOT);                                                  \
  if (mtfg_queue_position == 0) {                                                             \
    range = FreqMtfgQueuePos[Context][0] * (range / RangeScaleMtfgQueuePos[Context]);         \
    FreqMtfgQueuePos[Context][0] += UP_FREQ_MTFG_QUEUE_POS;                                   \
  }                                                                                           \
  else {                                                                                      \
    RangeLow = FreqMtfgQueuePos[Context][0];                                                  \
    FoundIndex = 1;                                                                           \
    while (FoundIndex != mtfg_queue_position)                                                 \
      RangeLow += FreqMtfgQueuePos[Context][FoundIndex++];                                    \
    low += RangeLow * (range /= RangeScaleMtfgQueuePos[Context]);                             \
    range *= FreqMtfgQueuePos[Context][FoundIndex];                                           \
    FreqMtfgQueuePos[Context][FoundIndex] += UP_FREQ_MTFG_QUEUE_POS;                          \
  }                                                                                           \
  if ((RangeScaleMtfgQueuePos[Context] += UP_FREQ_MTFG_QUEUE_POS) > FREQ_MTFG_QUEUE_POS_BOT)  \
    rescaleMtfgQueuePos(Context);                                                             \
}
#define EncodeSID(Context) {                                         \
  NormalizeEncoder(FREQ_SID_BOT);                                    \
  if (SIDSymbol == 0) {                                              \
    range = FreqSID[Context][0] * (range / RangeScaleSID[Context]);  \
    FreqSID[Context][0] += UP_FREQ_SID;                              \
  }                                                                  \
  else {                                                             \
    RangeLow = FreqSID[Context][0];                                  \
    Symbol = 1;                                                      \
    while (Symbol != SIDSymbol)                                      \
      RangeLow += FreqSID[Context][Symbol++];                        \
    low += RangeLow * (range /= RangeScaleSID[Context]);             \
    range *= FreqSID[Context][SIDSymbol];                            \
    FreqSID[Context][SIDSymbol] += UP_FREQ_SID;                      \
  }                                                                  \
  if ((RangeScaleSID[Context] += UP_FREQ_SID) > FREQ_SID_BOT)        \
    rescaleSID(Context);                                             \
}
#define EncodeExtraLength() {  \
  NormalizeEncoder(1 << 2);    \
  range >>= 2;                 \
  low += Symbol * range;       \
}
#define EncodeINST(Context) {                                                                \
  NormalizeEncoder(FREQ_INST_BOT);                                                           \
  if (Symbol == 0) {                                                                         \
    range = FreqINST[Context][SIDSymbol][0] * (range / RangeScaleINST[Context][SIDSymbol]);  \
    FreqINST[Context][SIDSymbol][0] += UP_FREQ_INST;                                         \
  }                                                                                          \
  else {                                                                                     \
    RangeLow = FreqINST[Context][SIDSymbol][0];                                              \
    FoundIndex = 1;                                                                          \
    while (FoundIndex != Symbol)                                                             \
      RangeLow += FreqINST[Context][SIDSymbol][FoundIndex++];                                \
    low += RangeLow * (range /= RangeScaleINST[Context][SIDSymbol]);                         \
    range *= FreqINST[Context][SIDSymbol][FoundIndex];                                       \
    FreqINST[Context][SIDSymbol][FoundIndex] += UP_FREQ_INST;                                \
  }                                                                                          \
  if ((RangeScaleINST[Context][SIDSymbol] += UP_FREQ_INST) > FREQ_INST_BOT)                  \
    rescaleINST(Context);                                                                    \
}
#define EncodeERG(Context, Symbol) {                              \
  NormalizeEncoder(FREQ_ERG_BOT);                                 \
  if ((Symbol) == 0) {                                            \
    range = FreqERG[Context] * (range / RangeScaleERG[Context]);  \
    FreqERG[Context] += UP_FREQ_ERG;                              \
  }                                                               \
  else {                                                          \
    low += FreqERG[Context] * (range /= RangeScaleERG[Context]);  \
    range *= RangeScaleERG[Context] - FreqERG[Context];           \
  }                                                               \
  if ((RangeScaleERG[Context] += UP_FREQ_ERG) > FREQ_ERG_BOT)     \
      rescaleERG(Context);                                        \
}
#define EncodeWordTag(Symbol) {                                     \
  NormalizeEncoder(FREQ_WORD_TAG_BOT);                              \
  if (Symbol == 0) {                                                \
    range = FreqWordTag * (range / RangeScaleWordTag);              \
    FreqWordTag += UP_FREQ_WORD_TAG;                                \
  }                                                                 \
  else {                                                            \
    low += FreqWordTag * (range /= RangeScaleWordTag);              \
    range *= RangeScaleWordTag - FreqWordTag;                       \
  }                                                                 \
  if ((RangeScaleWordTag += UP_FREQ_WORD_TAG) > FREQ_WORD_TAG_BOT)  \
      rescaleWordTag();                                             \
}
#define EncodeShortDictionarySymbol(Length, CodeBins) {  \
  NormalizeEncoder(1 << 12);                             \
  low += BinNum * (range /= DictionaryBins);             \
  range = CodeBins * (range << (12 - (Length)));         \
}
#define EncodeLongDictionarySymbol(CodeBins) {   \
  NormalizeEncoder(1 << 12);                     \
  low += BinNum * (range /= DictionaryBins);     \
  NormalizeEncoder(1 << (CodeLength - 12));      \
  low += BinCode * (range >>= CodeLength - 12);  \
  range *= CodeBins;                             \
}
#define EncodeBaseSymbol(Bits) {         \
  NormalizeEncoder(1 << Bits);           \
  low += BaseSymbol * (range >>= Bits);  \
}
#define EncodeFirstChar(SymType, LastChar) {                                                                \
  NormalizeEncoder(FREQ_FIRST_CHAR_BOT);                                                                    \
  if (Symbol == SymbolFirstChar[SymType][LastChar][0]) {                                                    \
    range = FreqFirstChar[SymType][LastChar][0] * (range / RangeScaleFirstChar[SymType][LastChar]);         \
    FreqFirstChar[SymType][LastChar][0] += UP_FREQ_FIRST_CHAR;                                              \
  }                                                                                                         \
  else {                                                                                                    \
    RangeLow = FreqFirstChar[SymType][LastChar][0];                                                         \
    FoundIndex = 1;                                                                                         \
    while (SymbolFirstChar[SymType][LastChar][FoundIndex] != Symbol)                                        \
      RangeLow += FreqFirstChar[SymType][LastChar][FoundIndex++];                                           \
    low += RangeLow * (range /= RangeScaleFirstChar[SymType][LastChar]);                                    \
    range *= FreqFirstChar[SymType][LastChar][FoundIndex];                                                  \
    FreqFirstChar[SymType][LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;                                     \
    if (FreqFirstChar[SymType][LastChar][FoundIndex] > FreqFirstChar[SymType][LastChar][FoundIndex-1]) {    \
      unsigned short int SavedFreq = FreqFirstChar[SymType][LastChar][FoundIndex];                          \
      do {                                                                                                  \
        FreqFirstChar[SymType][LastChar][FoundIndex] = FreqFirstChar[SymType][LastChar][FoundIndex-1];      \
        SymbolFirstChar[SymType][LastChar][FoundIndex] = SymbolFirstChar[SymType][LastChar][FoundIndex-1];  \
      } while ((--FoundIndex) && (SavedFreq > FreqFirstChar[SymType][LastChar][FoundIndex-1]));             \
      FreqFirstChar[SymType][LastChar][FoundIndex] = SavedFreq;                                             \
      SymbolFirstChar[SymType][LastChar][FoundIndex] = Symbol;                                              \
    }                                                                                                       \
  }                                                                                                         \
  if ((RangeScaleFirstChar[SymType][LastChar] += UP_FREQ_FIRST_CHAR) > FREQ_FIRST_CHAR_BOT)                 \
    rescaleFirstChar(SymType, LastChar);                                                                    \
}
#define EncodeFirstCharBinary(LastChar) {                                                         \
  NormalizeEncoder(FREQ_FIRST_CHAR_BOT);                                                          \
  if (RangeScaleFirstCharSection[LastChar][3] > count) {                                          \
    RangeScaleFirstCharSection[LastChar][3] += UP_FREQ_FIRST_CHAR;                                \
    if (RangeScaleFirstCharSection[LastChar][1] > count) {                                        \
      RangeScaleFirstCharSection[LastChar][1] += UP_FREQ_FIRST_CHAR;                              \
      if (RangeScaleFirstCharSection[LastChar][0] > count) {                                      \
        RangeScaleFirstCharSection[LastChar][0] += UP_FREQ_FIRST_CHAR;                            \
        if (Symbol == 0) {                                                                        \
          range = FreqFirstCharBinary[LastChar][0] * (range / RangeScaleFirstChar[0][LastChar]);  \
          FreqFirstCharBinary[LastChar][0] += UP_FREQ_FIRST_CHAR;                                 \
        }                                                                                         \
        else {                                                                                    \
          RangeLow = FreqFirstCharBinary[LastChar][0];                                            \
          FoundIndex = 1;                                                                         \
          while (FoundIndex != Symbol)                                                            \
            RangeLow += FreqFirstCharBinary[LastChar][FoundIndex++];                              \
          low += RangeLow * (range /= RangeScaleFirstChar[0][LastChar]);                          \
          range *= FreqFirstCharBinary[LastChar][FoundIndex];                                     \
          FreqFirstCharBinary[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;                        \
        }                                                                                         \
      }                                                                                           \
      else {                                                                                      \
        RangeLow = RangeScaleFirstCharSection[LastChar][0];                                       \
        FoundIndex = 0x20;                                                                        \
        while (FoundIndex != Symbol)                                                              \
          RangeLow += FreqFirstCharBinary[LastChar][FoundIndex++];                                \
        low += RangeLow * (range /= RangeScaleFirstChar[0][LastChar]);                            \
        range *= FreqFirstCharBinary[LastChar][FoundIndex];                                       \
        FreqFirstCharBinary[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;                          \
      }                                                                                           \
    }                                                                                             \
    else {                                                                                        \
      RangeLow = RangeScaleFirstCharSection[LastChar][1];                                         \
      if (RangeScaleFirstCharSection[LastChar][2] > count) {                                      \
        RangeScaleFirstCharSection[LastChar][2] += UP_FREQ_FIRST_CHAR;                            \
        FoundIndex = 0x40;                                                                        \
        while (FoundIndex != Symbol)                                                              \
          RangeLow += FreqFirstCharBinary[LastChar][FoundIndex++];                                \
        low += RangeLow * (range /= RangeScaleFirstChar[0][LastChar]);                            \
        range *= FreqFirstCharBinary[LastChar][FoundIndex];                                       \
        FreqFirstCharBinary[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;                          \
      }                                                                                           \
      else {                                                                                      \
        RangeLow += RangeScaleFirstCharSection[LastChar][2];                                      \
        FoundIndex = 0x60;                                                                        \
        while (FoundIndex != Symbol)                                                              \
          RangeLow += FreqFirstCharBinary[LastChar][FoundIndex++];                                \
        low += RangeLow * (range /= RangeScaleFirstChar[0][LastChar]);                            \
        range *= FreqFirstCharBinary[LastChar][FoundIndex];                                       \
        FreqFirstCharBinary[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;                          \
      }                                                                                           \
    }                                                                                             \
  }                                                                                               \
  else {                                                                                          \
    RangeLow = RangeScaleFirstCharSection[LastChar][3];                                           \
    if (RangeLow + RangeScaleFirstCharSection[LastChar][5] > count) {                             \
      RangeScaleFirstCharSection[LastChar][5] += UP_FREQ_FIRST_CHAR;                              \
      if (RangeScaleFirstCharSection[LastChar][4] > count) {                                      \
        RangeScaleFirstCharSection[LastChar][4] += UP_FREQ_FIRST_CHAR;                            \
        FoundIndex = 0x80;                                                                        \
        while (FoundIndex != Symbol)                                                              \
          RangeLow += FreqFirstCharBinary[LastChar][FoundIndex++];                                \
        low += RangeLow * (range /= RangeScaleFirstChar[0][LastChar]);                            \
        range *= FreqFirstCharBinary[LastChar][FoundIndex];                                       \
        FreqFirstCharBinary[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;                          \
      }                                                                                           \
      else {                                                                                      \
        RangeLow += RangeScaleFirstCharSection[LastChar][4];                                      \
        FoundIndex = 0xA0;                                                                        \
        while (FoundIndex != Symbol)                                                              \
          RangeLow += FreqFirstCharBinary[LastChar][FoundIndex++];                                \
        low += RangeLow * (range /= RangeScaleFirstChar[0][LastChar]);                            \
        range *= FreqFirstCharBinary[LastChar][FoundIndex];                                       \
        FreqFirstCharBinary[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;                          \
      }                                                                                           \
    }                                                                                             \
    else {                                                                                        \
      RangeLow += RangeScaleFirstCharSection[LastChar][5];                                        \
      if (RangeScaleFirstCharSection[LastChar][6] > count) {                                      \
        RangeScaleFirstCharSection[LastChar][6] += UP_FREQ_FIRST_CHAR;                            \
        FoundIndex = 0xC0;                                                                        \
        while (FoundIndex != Symbol)                                                              \
          RangeLow += FreqFirstCharBinary[LastChar][FoundIndex++];                                \
        low += RangeLow * (range /= RangeScaleFirstChar[0][LastChar]);                            \
        range *= FreqFirstCharBinary[LastChar][FoundIndex];                                       \
        FreqFirstCharBinary[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;                          \
      }                                                                                           \
      else {                                                                                      \
        RangeLow += RangeScaleFirstCharSection[LastChar][6];                                      \
        FoundIndex = 0xE0;                                                                        \
        while (FoundIndex != Symbol)                                                              \
          RangeLow += FreqFirstCharBinary[LastChar][FoundIndex++];                                \
        low += RangeLow * (range /= RangeScaleFirstChar[0][LastChar]);                            \
        range *= FreqFirstCharBinary[LastChar][FoundIndex];                                       \
        FreqFirstCharBinary[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;                          \
      }                                                                                           \
    }                                                                                             \
  }                                                                                               \
  if ((RangeScaleFirstChar[0][LastChar] += UP_FREQ_FIRST_CHAR) > FREQ_FIRST_CHAR_BOT)             \
    rescaleFirstCharBinary(LastChar);                                                             \
}
void InitEncoder(FILE* EncodedFile, unsigned char num_inst_codes) {
  OutFile = EncodedFile;
  OutCharNum = 0;
  OutBuffer = OutBuffer0;
  OutBufferNum = 0;
  low = 0, range = -1;
  StartModelSymType();
  StartModelMtfQueueNum();
  StartModelMtfQueuePos();
  StartModelMtfgQueuePos();
  StartModelSID();
  StartModelINST(num_inst_codes);
  StartModelERG();
  StartModelWordTag();
  StartModelFirstChar();
  StartModelFirstCharBinary();
}
void FinishEncoder() {
  while (low ^ (low + range)) {
    WriteByte(low >> 24, OutFile);
    low <<= 8;
    range <<= 8;
  }
  fwrite(OutBuffer,1,OutCharNum,OutFile);
}
#endif
#ifdef decode
#define ReadByte(File) {                          \
  if (InCharNum != NumInChar)                     \
    Symbol = InBuffer[InCharNum++];               \
  else {                                          \
    NumInChar = fread(InBuffer,1,BUF_SIZE,File);  \
    Symbol = InBuffer[0];                         \
    InCharNum = 1;                                \
  }                                               \
}
#define NormalizeDecoder(bot) {                                                                \
  while ((low ^ (low + range)) < TOP || range < (bot) && ((range = -low & ((bot) - 1)), 1)) {  \
    ReadByte(InFile);                                                                          \
    code = (code << 8) | Symbol;                                                               \
    low <<= 8;                                                                                 \
    range <<= 8;                                                                               \
  }                                                                                            \
}
#define DecodeSymTypeStart(Context) {                                        \
  NormalizeDecoder(FREQ_SYM_TYPE_BOT);                                       \
  count = (code - low) / (range /= RangeScaleSymType[Context]);              \
}
#define DecodeSymTypeCheckType0(Context) (FreqSymType[Context][0] > count)
#define DecodeSymTypeFinishType0(Context) {                                  \
  range *= FreqSymType[Context][0];                                          \
  FreqSymType[Context][0] += UP_FREQ_SYM_TYPE;                               \
  if ((RangeScaleSymType[Context] += UP_FREQ_SYM_TYPE) > FREQ_SYM_TYPE_BOT)  \
    rescaleSymType(Context);                                                 \
}
#define DecodeSymTypeCheckType1(Context) ((RangeHigh = FreqSymType[Context][0] + FreqSymType[Context][1]) > count)
#define DecodeSymTypeFinishType1(Context) {                                  \
  low += range * FreqSymType[Context][0];                                    \
  range *= FreqSymType[Context][1];                                          \
  FreqSymType[Context][1] += UP_FREQ_SYM_TYPE;                               \
  if ((RangeScaleSymType[Context] += UP_FREQ_SYM_TYPE) > FREQ_SYM_TYPE_BOT)  \
    rescaleSymType(Context);                                                 \
}
#define DecodeSymTypeCheckType2(Context) ((RangeHigh + FreqSymType[Context][2]) > count)
#define DecodeSymTypeFinishType2(Context) {                                  \
  low += range * RangeHigh;                                                  \
  range *= FreqSymType[Context][2];                                          \
  FreqSymType[Context][2] += UP_FREQ_SYM_TYPE;                               \
  if ((RangeScaleSymType[Context] += UP_FREQ_SYM_TYPE) > FREQ_SYM_TYPE_BOT)  \
    rescaleSymType(Context);                                                 \
}
#define DecodeSymTypeFinishType3(Context) {                                  \
  low += range * (RangeHigh + FreqSymType[Context][2]);                      \
  range *= FreqSymType[Context][3];                                          \
  FreqSymType[Context][3] += UP_FREQ_SYM_TYPE;                               \
  if ((RangeScaleSymType[Context] += UP_FREQ_SYM_TYPE) > FREQ_SYM_TYPE_BOT)  \
    rescaleSymType(Context);                                                 \
}
#define DecodeMtfQueueNumStart(Context) {                                     \
  NormalizeDecoder(FREQ_MTF_QUEUE_NUM_BOT);                                   \
  count = (code - low) / (range /= RangeScaleMtfQueueNum[Context]);           \
}
#define DecodeMtfQueueNumCheck0(Context) ((RangeHigh = FreqMtfQueueNum[Context][0]) > count)
#define DecodeMtfQueueNumFinish0(Context) range *= RangeHigh;
#define DecodeMtfQueueNumFinish(Context) {                                    \
  mtf_queue_number = 1;                                                       \
  while ((RangeHigh += FreqMtfQueueNum[Context][mtf_queue_number]) <= count)  \
    mtf_queue_number++;                                                       \
  low += range * (RangeHigh - FreqMtfQueueNum[Context][mtf_queue_number]);    \
  range *= FreqMtfQueueNum[Context][mtf_queue_number];                        \
}
#define DecodeMtfQueuePosStart(Context, mtf_queue_number) {                                                  \
  NormalizeDecoder(FREQ_MTF_QUEUE_POS_BOT);                                                                  \
  unsigned short int RangeScale = RangeScaleMtfQueuePos[Context][mtf_queue_number];                          \
  if (mtf_queue_size[mtf_queue_number+2] != MTF_QUEUE_SIZE) {                                                \
    unsigned char tqp = MTF_QUEUE_SIZE - 1;                                                                  \
    do {                                                                                                     \
      RangeScale -= FreqMtfQueuePos[Context][mtf_queue_number][tqp];                                         \
    } while (tqp-- != mtf_queue_size[mtf_queue_number+2]);                                                   \
  }                                                                                                          \
  count = (code - low) / (range /= RangeScale);                                                              \
}
#define DecodeMtfQueuePosCheck0(Context, mtf_queue_number) ((RangeHigh = FreqMtfQueuePos[Context][mtf_queue_number][0]) > count) 
#define DecodeMtfQueuePosFinish0(Context, mtf_queue_number) {                                                \
  range *= RangeHigh;                                                                                        \
  FreqMtfQueuePos[Context][mtf_queue_number][0] = RangeHigh + UP_FREQ_MTF_QUEUE_POS;                         \
  if ((RangeScaleMtfQueuePos[Context][mtf_queue_number] += UP_FREQ_MTF_QUEUE_POS) > FREQ_MTF_QUEUE_POS_BOT)  \
    rescaleMtfQueuePos(Context, mtf_queue_number);                                                           \
}
#define DecodeMtfQueuePosFinish(Context, mtf_queue_number) {                                                 \
  Symbol = 1;                                                                                                \
  while ((RangeHigh += FreqMtfQueuePos[Context][mtf_queue_number][Symbol]) <= count)                         \
    Symbol++;                                                                                                \
  low += range * (RangeHigh - FreqMtfQueuePos[Context][mtf_queue_number][Symbol]);                           \
  range *= FreqMtfQueuePos[Context][mtf_queue_number][Symbol];                                               \
  FreqMtfQueuePos[Context][mtf_queue_number][Symbol] += UP_FREQ_MTF_QUEUE_POS;                               \
  if ((RangeScaleMtfQueuePos[Context][mtf_queue_number] += UP_FREQ_MTF_QUEUE_POS) > FREQ_MTF_QUEUE_POS_BOT)  \
    rescaleMtfQueuePos(Context, mtf_queue_number);                                                           \
}
#define DecodeMtfgQueuePosStart(Context) {                                                    \
  NormalizeDecoder(FREQ_MTFG_QUEUE_POS_BOT);                                                  \
  count = (code - low) / (range /= RangeScaleMtfgQueuePos[Context]);                          \
}
#define DecodeMtfgQueuePosCheck0(Context) ((RangeHigh = FreqMtfgQueuePos[Context][0]) > count)
#define DecodeMtfgQueuePosFinish0(Context) {                                                  \
  range *= RangeHigh;                                                                         \
  FreqMtfgQueuePos[Context][0] = RangeHigh + UP_FREQ_MTFG_QUEUE_POS;                          \
  mtfg_queue_position = 0;                                                                    \
  if ((RangeScaleMtfgQueuePos[Context] += UP_FREQ_MTFG_QUEUE_POS) > FREQ_MTFG_QUEUE_POS_BOT)  \
    rescaleMtfgQueuePos(Context);                                                             \
}
#define DecodeMtfgQueuePosFinish(Context) {                                                   \
  mtfg_queue_position = 1;                                                                    \
  while ((RangeHigh += FreqMtfgQueuePos[Context][mtfg_queue_position]) <= count)              \
    mtfg_queue_position++;                                                                    \
  low += range * (RangeHigh - FreqMtfgQueuePos[Context][mtfg_queue_position]);                \
  range *= FreqMtfgQueuePos[Context][mtfg_queue_position];                                    \
  FreqMtfgQueuePos[Context][mtfg_queue_position] += UP_FREQ_MTFG_QUEUE_POS;                   \
  if ((RangeScaleMtfgQueuePos[Context] += UP_FREQ_MTFG_QUEUE_POS) > FREQ_MTFG_QUEUE_POS_BOT)  \
    rescaleMtfgQueuePos(Context);                                                             \
}
#define DecodeSIDStart(Context) {                              \
  NormalizeDecoder(FREQ_SID_BOT);                              \
  count = (code - low) / (range /= RangeScaleSID[Context]);    \
}
#define DecodeSIDCheck0(Context) ((RangeHigh = FreqSID[Context][0]) > count)
#define DecodeSIDFinish0(Context) {                            \
  range *= RangeHigh;                                          \
  FreqSID[Context][0] = RangeHigh + UP_FREQ_SID;               \
  SIDSymbol = 0;                                               \
  if ((RangeScaleSID[Context] += UP_FREQ_SID) > FREQ_SID_BOT)  \
    rescaleSID(Context);                                       \
}
#define DecodeSIDFinish(Context) {                             \
  SIDSymbol = 1;                                               \
  while ((RangeHigh += FreqSID[Context][SIDSymbol]) <= count)  \
    SIDSymbol++;                                               \
  low += range * (RangeHigh - FreqSID[Context][SIDSymbol]);    \
  range *= FreqSID[Context][SIDSymbol];                        \
  FreqSID[Context][SIDSymbol] += UP_FREQ_SID;                  \
  if ((RangeScaleSID[Context] += UP_FREQ_SID) > FREQ_SID_BOT)  \
    rescaleSID(Context);                                       \
}
#define DecodeExtraLength() {             \
  NormalizeDecoder(1 << 2);               \
  Symbol = (code - low) / (range >>= 2);  \
  low += range * Symbol;                  \
}
#define DecodeINSTStart(Context) {                                           \
  NormalizeDecoder(FREQ_INST_BOT);                                           \
  count = (code - low) / (range /= RangeScaleINST[Context][SIDSymbol]);      \
}
#define DecodeINSTCheck0(Context) ((RangeHigh = FreqINST[Context][SIDSymbol][0]) > count)
#define DecodeINSTFinish0(Context) {                                         \
  range *= RangeHigh;                                                        \
  FreqINST[Context][SIDSymbol][0] = RangeHigh + UP_FREQ_INST;                \
  if ((RangeScaleINST[Context][SIDSymbol] += UP_FREQ_INST) > FREQ_INST_BOT)  \
    rescaleINST(Context);                                                    \
}
#define DecodeINSTFinish(Context) {                                          \
  Instances = 1;                                                             \
  while ((RangeHigh += FreqINST[Context][SIDSymbol][Instances]) <= count)    \
    Instances++;                                                             \
  low += range * (RangeHigh - FreqINST[Context][SIDSymbol][Instances]);      \
  range *= FreqINST[Context][SIDSymbol][Instances];                          \
  FreqINST[Context][SIDSymbol][Instances] += UP_FREQ_INST;                   \
  if ((RangeScaleINST[Context][SIDSymbol] += UP_FREQ_INST) > FREQ_INST_BOT)  \
    rescaleINST(Context);                                                    \
}
#define DecodeERG(Context) {                                   \
  NormalizeDecoder(FREQ_ERG_BOT);                              \
  count = (code - low) / (range /= RangeScaleERG[Context]);    \
  if (FreqERG[Context] > count) {                              \
    range *= FreqERG[Context];                                 \
    FreqERG[Context] += UP_FREQ_ERG;                           \
    nonergodic = 0;                                            \
  }                                                            \
  else {                                                       \
    low += range * FreqERG[Context];                           \
    range *= RangeScaleERG[Context] - FreqERG[Context];        \
    nonergodic = 1;                                            \
  }                                                            \
  if ((RangeScaleERG[Context] += UP_FREQ_ERG) > FREQ_ERG_BOT)  \
    rescaleERG(Context);                                       \
}
#define DecodeWordTag() {                                           \
  NormalizeDecoder(FREQ_WORD_TAG_BOT);                              \
  count = (code - low) / (range /= RangeScaleWordTag);              \
  if (FreqWordTag > count) {                                        \
    range *= FreqWordTag;                                           \
    FreqWordTag += UP_FREQ_WORD_TAG;                                \
    Symbol = 0;                                                     \
  }                                                                 \
  else {                                                            \
    low += range * FreqWordTag;                                     \
    range *= RangeScaleWordTag - FreqWordTag;                       \
    Symbol = 1;                                                     \
  }                                                                 \
  if ((RangeScaleWordTag += UP_FREQ_WORD_TAG) > FREQ_WORD_TAG_BOT)  \
    rescaleWordTag();                                               \
}
#define DecodeDictionaryBin(lookup_bits) {                                      \
  NormalizeDecoder(1 << 12);                                                    \
  CodeLength = lookup_bits[BinNum = (code - low) / (range /= DictionaryBins)];  \
  char BitsUnderBinSize = bin_bits_under_max[FirstChar] - CodeLength;           \
  if (BitsUnderBinSize >= 0)                                                    \
    low += (range <<= BitsUnderBinSize) * (BinNum >> BitsUnderBinSize);         \
  else                                                                          \
    low += range * BinNum;                                                      \
}
#define DecodeDictionarySymbolIndex(Bits,FirstBin,SymbolArray) {               \
  NormalizeDecoder(1 << (Bits));                                               \
  BinCode = (code - low) / (range >>= (Bits));                                 \
  SymbolIndex = (1 << (Bits)) * (BinNum - FirstBin) + BinCode;                 \
  if (SymbolIndex >= min_extra_reduce_index) {                                 \
    BinCode &= -2;                                                             \
    SymbolIndex = (SymbolIndex + min_extra_reduce_index) >> 1;                 \
    if (CodeLength <= max_regular_code_length) {                               \
      unsigned int index = SymbolIndex;                                        \
      unsigned int extra_code_bins = 0;                                        \
      while (BinCode && (symbol_data[SymbolArray[--index]].type & 8)) {        \
        char bins = (index >= min_extra_reduce_index) ? 2 : 1;                 \
        extra_code_bins += bins;                                               \
        BinCode -= bins;                                                       \
      }                                                                        \
      low += range * BinCode;                                                  \
      unsigned int * SymbolArrayPtr = &SymbolArray[SymbolIndex];               \
      while (symbol_data[*SymbolArrayPtr].type & 8) {                          \
        extra_code_bins += 2;                                                  \
        SymbolArrayPtr++;                                                      \
      }                                                                        \
      range *= 2 + extra_code_bins;                                            \
      symbol_number = *SymbolArrayPtr;                                         \
    }                                                                          \
    else {                                                                     \
      low += range * BinCode;                                                  \
      range <<= 1;                                                             \
      symbol_number = SymbolArray[SymbolIndex];                                \
    }                                                                          \
  }                                                                            \
  else {                                                                       \
    if (CodeLength <= max_regular_code_length) {                               \
      unsigned int * SymbolArrayPtr = &SymbolArray[SymbolIndex];               \
      unsigned int OrigBinCode = BinCode;                                      \
      while (BinCode && (symbol_data[*(--SymbolArrayPtr)].type & 8))           \
        BinCode--;                                                             \
      unsigned int extra_code_bins = OrigBinCode - BinCode;                    \
      low += range * BinCode;                                                  \
      while (symbol_data[SymbolArray[SymbolIndex]].type & 8)                   \
        extra_code_bins += (++SymbolIndex >= min_extra_reduce_index) ? 2 : 1;  \
      range *= 1 + extra_code_bins;                                            \
      symbol_number = SymbolArray[SymbolIndex];                                \
    }                                                                          \
    else {                                                                     \
      low += range * BinCode;                                                  \
      symbol_number = SymbolArray[SymbolIndex];                                \
    }                                                                          \
  }                                                                            \
}
#define DecodeBaseSymbol(Bits) {                                  \
  NormalizeDecoder(1 << Bits);                                    \
  low += range * (BaseSymbol = (code - low) / (range >>= Bits));  \
}
#define DecodeFirstChar(SymType, LastChar) {                                                        \
  NormalizeDecoder(FREQ_FIRST_CHAR_BOT);                                                            \
  count = (code - low) / (range /= RangeScaleFirstChar[SymType][LastChar]);                         \
  if ((RangeHigh = FreqFirstChar[SymType][LastChar][0]) > count) {                                  \
    range *= RangeHigh;                                                                             \
    FreqFirstChar[SymType][LastChar][0] = RangeHigh + UP_FREQ_FIRST_CHAR;                           \
    FirstChar = SymbolFirstChar[SymType][LastChar][0];                                              \
  }                                                                                                 \
  else {                                                                                            \
    unsigned short int * FreqPtr = &FreqFirstChar[SymType][LastChar][1];                            \
    while ((RangeHigh += *FreqPtr) <= count)                                                        \
      FreqPtr++;                                                                                    \
    low += range * (RangeHigh - *FreqPtr);                                                          \
    range *= *FreqPtr;                                                                              \
    *FreqPtr += UP_FREQ_FIRST_CHAR;                                                                 \
    FoundIndex = FreqPtr - &FreqFirstChar[SymType][LastChar][0];                                    \
    FirstChar = SymbolFirstChar[SymType][LastChar][FoundIndex];                                     \
    if (*FreqPtr > *(FreqPtr - 1)) {                                                                \
      unsigned short int SavedFreq = *FreqPtr;                                                      \
      unsigned char * SymbolPtr = &SymbolFirstChar[SymType][LastChar][FoundIndex];                  \
      do {                                                                                          \
        *FreqPtr = *(FreqPtr - 1);                                                                  \
        FreqPtr--;                                                                                  \
        *SymbolPtr = *(SymbolPtr - 1);                                                              \
        SymbolPtr--;                                                                                \
      } while ((FreqPtr != &FreqFirstChar[SymType][LastChar][0]) && (SavedFreq > *(FreqPtr - 1)));  \
      *FreqPtr = SavedFreq;                                                                         \
      *SymbolPtr = FirstChar;                                                                       \
    }                                                                                               \
  }                                                                                                 \
  if ((RangeScaleFirstChar[SymType][LastChar] += UP_FREQ_FIRST_CHAR) > FREQ_FIRST_CHAR_BOT)         \
    rescaleFirstChar(SymType, LastChar);                                                            \
}
#define DecodeFirstCharBinary(LastChar) {                                                \
  NormalizeDecoder(FREQ_FIRST_CHAR_BOT);                                                 \
  count = (code - low) / (range /= RangeScaleFirstChar[0][LastChar]);                    \
  unsigned short int * FreqPtr;                                                          \
  if (RangeScaleFirstCharSection[LastChar][3] > count) {                                 \
    RangeScaleFirstCharSection[LastChar][3] += UP_FREQ_FIRST_CHAR;                       \
    if (RangeScaleFirstCharSection[LastChar][1] > count) {                               \
      RangeScaleFirstCharSection[LastChar][1] += UP_FREQ_FIRST_CHAR;                     \
      if (RangeScaleFirstCharSection[LastChar][0] > count) {                             \
        RangeHigh = 0;                                                                   \
        RangeScaleFirstCharSection[LastChar][0] += UP_FREQ_FIRST_CHAR;                   \
        FreqPtr = &FreqFirstCharBinary[LastChar][0];                                     \
      }                                                                                  \
      else {                                                                             \
        RangeHigh = RangeScaleFirstCharSection[LastChar][0];                             \
        FreqPtr = &FreqFirstCharBinary[LastChar][0x20];                                  \
      }                                                                                  \
    }                                                                                    \
    else {                                                                               \
      RangeHigh = RangeScaleFirstCharSection[LastChar][1];                               \
      if (RangeHigh + RangeScaleFirstCharSection[LastChar][2] > count) {                 \
        RangeScaleFirstCharSection[LastChar][2] += UP_FREQ_FIRST_CHAR;                   \
        FreqPtr = &FreqFirstCharBinary[LastChar][0x40];                                  \
      }                                                                                  \
      else {                                                                             \
        RangeHigh += RangeScaleFirstCharSection[LastChar][2];                            \
        FreqPtr = &FreqFirstCharBinary[LastChar][0x60];                                  \
      }                                                                                  \
    }                                                                                    \
  }                                                                                      \
  else {                                                                                 \
    RangeHigh = RangeScaleFirstCharSection[LastChar][3];                                 \
    if (RangeHigh + RangeScaleFirstCharSection[LastChar][5] > count) {                   \
      RangeScaleFirstCharSection[LastChar][5] += UP_FREQ_FIRST_CHAR;                     \
      if (RangeHigh + RangeScaleFirstCharSection[LastChar][4] > count) {                 \
        RangeScaleFirstCharSection[LastChar][4] += UP_FREQ_FIRST_CHAR;                   \
        FreqPtr = &FreqFirstCharBinary[LastChar][0x80];                                  \
      }                                                                                  \
      else {                                                                             \
        RangeHigh += RangeScaleFirstCharSection[LastChar][4];                            \
        FreqPtr = &FreqFirstCharBinary[LastChar][0xA0];                                  \
      }                                                                                  \
    }                                                                                    \
    else {                                                                               \
      RangeHigh += RangeScaleFirstCharSection[LastChar][5];                              \
      if (RangeHigh + RangeScaleFirstCharSection[LastChar][6] > count) {                 \
        RangeScaleFirstCharSection[LastChar][6] += UP_FREQ_FIRST_CHAR;                   \
        FreqPtr = &FreqFirstCharBinary[LastChar][0xC0];                                  \
      }                                                                                  \
      else {                                                                             \
        RangeHigh += RangeScaleFirstCharSection[LastChar][6];                            \
        FreqPtr = &FreqFirstCharBinary[LastChar][0xE0];                                  \
      }                                                                                  \
    }                                                                                    \
  }                                                                                      \
  while ((RangeHigh += *FreqPtr) <= count)                                               \
    FreqPtr++;                                                                           \
  FirstChar = FreqPtr - &FreqFirstCharBinary[LastChar][0];                               \
  low += range * (RangeHigh - *FreqPtr);                                                 \
  range *= *FreqPtr;                                                                     \
  *FreqPtr += UP_FREQ_FIRST_CHAR;                                                        \
  if ((RangeScaleFirstChar[0][LastChar] += UP_FREQ_FIRST_CHAR) > FREQ_FIRST_CHAR_BOT) {  \
    rescaleFirstCharBinary(LastChar);                                                    \
  }                                                                                      \
}
void InitDecoder(FILE* EncodedFile, unsigned char num_inst_codes) {
  InFile = EncodedFile;
  NumInChar = 0, InCharNum = 0, OutCharNum = 0;
  code = 0, range = -1;
  for (low = 4; low != 0; low--) {
    ReadByte(InFile);
    code = (code << 8) | Symbol;
  }
  StartModelSymType();
  StartModelMtfQueueNum();
  StartModelMtfQueuePos();
  StartModelMtfgQueuePos();
  StartModelSID();
  StartModelINST(num_inst_codes);
  StartModelERG();
  StartModelWordTag();
  StartModelFirstChar();
  StartModelFirstCharBinary();
}
#endif

