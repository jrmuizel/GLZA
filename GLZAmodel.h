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
enum { UP_FREQ_SYM_TYPE = 1, FREQ_SYM_TYPE_BOT = 0x80 };
enum { UP_FREQ_MTF_QUEUE_NUM2 = 4, UP_FREQ_MTF_QUEUE_NUM = 10, FREQ_MTF_QUEUE_NUM_BOT = 0x100 };
enum { UP_FREQ_MTF_QUEUE_POS = 5, FREQ_MTF_QUEUE_POS_BOT = 0x4000 };
enum { UP_FREQ_MTFG_QUEUE_POS = 2, FREQ_MTFG_QUEUE_POS_BOT = 0x4000 };
enum { UP_FREQ_SID = 3, FREQ_SID_BOT = 0x1000 };
enum { UP_FREQ_INST = 8, FREQ_INST_BOT = 0x8000 };
enum { UP_FREQ_ERG = 1, FREQ_ERG_BOT = 0x20 };
enum { UP_FREQ_FIRST_CHAR = 1, FREQ_FIRST_CHAR_BOT = 0x2000 };
enum { NOT_CAP = 0, CAP = 1 };
enum { LEVEL0 = 0, LEVEL0_CAP = 1, LEVEL1 = 2, LEVEL1_CAP = 3 };

unsigned int NumInChar, InCharNum, OutCharNum;
unsigned int RangeLow, RangeHigh, count, BaseSymbol, SymbolIndex, BinCode, FirstChar, SymbolFirstChar[0x100][0x100];
unsigned int low, code, range;
unsigned char InData[BUF_SIZE], OutData[BUF_SIZE];
unsigned char Symbol, SIDSymbol, FoundIndex, mtfg_queue_position, mtf_queue_number, Instances, CodeLength;
unsigned char RangeScaleSymType[4], RangeScaleERG;
unsigned char FreqSymType[4][4], FreqERG0;
unsigned short int RangeScaleMtfQueueNum[2], RangeScaleMtfQueuePos[2][19], RangeScaleMtfgQueuePos[2];
unsigned short int RangeScaleSID[2], RangeScaleINST[2][16], RangeScaleFirstChar[0x100];
unsigned short int FreqMtfQueueNum[2][19], FreqMtfQueuePos[2][19][64], FreqMtfgQueuePos[2][256];
unsigned short int FreqSID[2][16], FreqINST[2][16][41], FreqFirstChar[0x100][0x100];
unsigned short int DictionaryBins, BinNum;
FILE * InFile, * OutFile;


#define StartModelSymType() {       \
  char i = 3;                       \
  do {                              \
    FreqSymType[i][0] = 1;          \
    FreqSymType[i][1] = 5;          \
    FreqSymType[i][2] = 1;          \
    FreqSymType[i][3] = 1;          \
    RangeScaleSymType[i] = 8;       \
  } while (i--);                    \
}
#define StartModelSymTypeNoMtf() {  \
  char i = 3;                       \
  do {                              \
    FreqSymType[i][0] = 1;          \
    FreqSymType[i][1] = 5;          \
    FreqSymType[i][2] = 0;          \
    FreqSymType[i][3] = 0;          \
    RangeScaleSymType[i] = 6;       \
  } while (i--);                    \
}
#define StartModelMtfQueueNum() {    \
  unsigned char i = 1;               \
  do {                               \
    unsigned char j = 18;            \
    do {                             \
      FreqMtfQueueNum[i][j] = 8;     \
    } while (j--);                   \
    RangeScaleMtfQueueNum[i] = 152;  \
  } while (i--);                     \
}
#define StartModelMtfQueuePos() {        \
  unsigned char i = 1;                   \
  do {                                   \
    unsigned char j = 18;                \
    do {                                 \
      unsigned char k = 63;              \
      do {                               \
        FreqMtfQueuePos[i][j][k] = 1;    \
      } while (k--);                     \
      RangeScaleMtfQueuePos[i][j] = 64;  \
    } while (j--);                       \
  } while (i--);                         \
}
#define StartModelMtfgQueuePos() {     \
  unsigned char i = 1;                 \
  do {                                 \
    unsigned char j = 0;               \
    do {                               \
      FreqMtfgQueuePos[i][j] = 128;    \
    } while (++j != 5);                \
    do {                               \
      FreqMtfgQueuePos[i][j] = 64;     \
    } while (++j != 8);                \
    do {                               \
      FreqMtfgQueuePos[i][j] = 32;     \
    } while (++j != 16);               \
    do {                               \
      FreqMtfgQueuePos[i][j] = 16;     \
    } while (++j != 32);               \
    do {                               \
      FreqMtfgQueuePos[i][j] = 8;      \
    } while (++j != 64);               \
    do {                               \
      FreqMtfgQueuePos[i][j] = 4;      \
    } while (++j != 128);              \
    do {                               \
      FreqMtfgQueuePos[i][j] = 2;      \
    } while (++j != 192);              \
    do {                               \
      FreqMtfgQueuePos[i][j] = 1;      \
    } while (++j);                     \
    RangeScaleMtfgQueuePos[i] = 2048;  \
  } while (i--);                       \
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
#define StartModelINST() {        \
  unsigned char i = 1;            \
  do {                            \
    unsigned char j = 15;         \
    do {                          \
      unsigned char k = 40;       \
      do {                        \
        FreqINST[i][j][k] = 1;    \
      } while (k--);              \
      RangeScaleINST[i][j] = 41;  \
    } while (j--);                \
  } while (i--);                  \
}
#define StartModelERG() {  \
  FreqERG0 = 1;            \
  RangeScaleERG = 2;       \
}
#define StartModelFirstChar() {      \
  unsigned char i = 0xFF;            \
  do {                               \
    unsigned char j = 0xFF;          \
    do {                             \
      FreqFirstChar[i][j] = 0;       \
    } while (j--);                   \
    RangeScaleFirstChar[i] = 0;      \
  } while (i--);                     \
}
#define rescaleSymType(Context) {                                                              \
  RangeScaleSymType[Context] = FreqSymType[Context][0] = (FreqSymType[Context][0] + 1) >> 1;   \
  RangeScaleSymType[Context] += FreqSymType[Context][1] = (FreqSymType[Context][1] + 1) >> 1;  \
  RangeScaleSymType[Context] += FreqSymType[Context][2] = (FreqSymType[Context][2] + 1) >> 1;  \
  RangeScaleSymType[Context] += FreqSymType[Context][3] = (FreqSymType[Context][3] + 1) >> 1;  \
}
#define rescaleMtfQueueNum(Context) {                                                                       \
  unsigned char i = 17;                                                                                     \
  RangeScaleMtfQueueNum[Context] = FreqMtfQueueNum[Context][18] -= (FreqMtfQueueNum[Context][18] >> 2);     \
  do {                                                                                                      \
    RangeScaleMtfQueueNum[Context] += (FreqMtfQueueNum[Context][i] -= (FreqMtfQueueNum[Context][i] >> 2));  \
  } while (i--);                                                                                            \
}
#define rescaleMtfQueuePos(Context) {                                                                  \
  unsigned char i = 62;                                                                                \
  RangeScaleMtfQueuePos[Context][mtf_queue_number] = (FreqMtfQueuePos[Context][mtf_queue_number][63]   \
      = (FreqMtfQueuePos[Context][mtf_queue_number][63] + 1) >> 1);                                    \
  do {                                                                                                 \
    RangeScaleMtfQueuePos[Context][mtf_queue_number] += FreqMtfQueuePos[Context][mtf_queue_number][i]  \
        = (FreqMtfQueuePos[Context][mtf_queue_number][i] + 1) >> 1;                                    \
  } while (i--);                                                                                       \
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
  unsigned char i = 39;                                                                                                  \
  RangeScaleINST[Context][SIDSymbol] = (FreqINST[Context][SIDSymbol][40] = (FreqINST[Context][SIDSymbol][40] + 1) >> 1); \
  do {                                                                                                                   \
    RangeScaleINST[Context][SIDSymbol] += FreqINST[Context][SIDSymbol][i] = (FreqINST[Context][SIDSymbol][i] + 1) >> 1;  \
  } while (i--);                                                                                                         \
}
#define rescaleERG() {                                    \
  RangeScaleERG = ((RangeScaleERG - FreqERG0) + 1) >> 1;  \
  RangeScaleERG += FreqERG0 = (FreqERG0 + 1) >> 1;        \
}
#define rescaleFirstChar(Context) {                                                                       \
  unsigned char i = 0xFE;                                                                                 \
  RangeScaleFirstChar[Context] = FreqFirstChar[Context][0xFF] = (FreqFirstChar[Context][0xFF] + 1) >> 1;  \
  do {                                                                                                    \
    RangeScaleFirstChar[Context] += FreqFirstChar[Context][i] = (FreqFirstChar[Context][i] + 1) >> 1;     \
  } while (i--);                                                                                          \
}
#define ReadByte(File) {                                 \
  if (InCharNum != NumInChar)                            \
    Symbol = InData[InCharNum++];                        \
  else if (NumInChar = fread(InData,1,BUF_SIZE,File)) {  \
    Symbol = InData[0];                                  \
    InCharNum = 1;                                       \
  }                                                      \
  else                                                   \
    Symbol = -1;                                         \
}
#define WriteByte(Value, File) {                   \
  OutData[OutCharNum++] = (unsigned char)(Value);  \
  if (OutCharNum == BUF_SIZE) {                    \
    fflush(File);                                  \
    fwrite(OutData,1,BUF_SIZE,File);               \
    OutCharNum = 0;                                \
  }                                                \
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
  if ((RangeScaleSymType[Context] += UP_FREQ_SYM_TYPE) >= FREQ_SYM_TYPE_BOT)                           \
    rescaleSymType(Context);                                                                           \
}
#define EncodeNewType(Context) {                                                                       \
  NormalizeEncoder(FREQ_SYM_TYPE_BOT);                                                                 \
  low += FreqSymType[Context][0] * (range /= RangeScaleSymType[Context]);                              \
  range *= FreqSymType[Context][1];                                                                    \
  FreqSymType[Context][1] += UP_FREQ_SYM_TYPE;                                                         \
  if ((RangeScaleSymType[Context] += UP_FREQ_SYM_TYPE) >= FREQ_SYM_TYPE_BOT)                           \
    rescaleSymType(Context);                                                                           \
}
#define EncodeMtfgType(Context) {                                                                      \
  NormalizeEncoder(FREQ_SYM_TYPE_BOT);                                                                 \
  low += (FreqSymType[Context][0] + FreqSymType[Context][1]) * (range /= RangeScaleSymType[Context]);  \
  range *= FreqSymType[Context][2];                                                                    \
  FreqSymType[Context][2] += UP_FREQ_SYM_TYPE;                                                         \
  if ((RangeScaleSymType[Context] += UP_FREQ_SYM_TYPE) >= FREQ_SYM_TYPE_BOT)                           \
    rescaleSymType(Context);                                                                           \
}
#define EncodeMtfType(Context) {                                                                       \
  NormalizeEncoder(FREQ_SYM_TYPE_BOT);                                                                 \
  low += (FreqSymType[Context][0] + FreqSymType[Context][1] + FreqSymType[Context][2])                 \
      * (range /= RangeScaleSymType[Context]);                                                         \
  range *= FreqSymType[Context][3];                                                                    \
  FreqSymType[Context][3] += UP_FREQ_SYM_TYPE;                                                         \
  if ((RangeScaleSymType[Context] += UP_FREQ_SYM_TYPE) >= FREQ_SYM_TYPE_BOT)                           \
    rescaleSymType(Context);                                                                           \
}
#define EncodeMtfQueueNum(Context) {                                                        \
  NormalizeEncoder(FREQ_MTF_QUEUE_NUM_BOT);                                                 \
  if (mtf_queue_number == 0) {                                                              \
    range = FreqMtfQueueNum[Context][0] * (range / RangeScaleMtfQueueNum[Context]);         \
    FreqMtfQueueNum[Context][0] += UP_FREQ_MTF_QUEUE_NUM;                                   \
  }                                                                                         \
  else {                                                                                    \
    RangeLow = FreqMtfQueueNum[Context][0];                                                 \
    FoundIndex = 1;                                                                         \
    while (FoundIndex != mtf_queue_number)                                                  \
      RangeLow += FreqMtfQueueNum[Context][FoundIndex++];                                   \
    low += RangeLow * (range /= RangeScaleMtfQueueNum[Context]);                            \
    range *= FreqMtfQueueNum[Context][FoundIndex];                                          \
    FreqMtfQueueNum[Context][FoundIndex] += UP_FREQ_MTF_QUEUE_NUM;                          \
  }                                                                                         \
  if ((RangeScaleMtfQueueNum[Context] += UP_FREQ_MTF_QUEUE_NUM) >= FREQ_MTF_QUEUE_NUM_BOT)  \
    rescaleMtfQueueNum(Context);                                                            \
}
#define EncodeMtfQueueNumLastSymbol(Context) {                                              \
  NormalizeEncoder(FREQ_MTF_QUEUE_NUM_BOT);                                                 \
  if (mtf_queue_number == 0)                                                                \
    range = FreqMtfQueueNum[Context][0] * (range / RangeScaleMtfQueueNum[Context]);         \
  else {                                                                                    \
    RangeLow = FreqMtfQueueNum[Context][0];                                                 \
    FoundIndex = 1;                                                                         \
    while (FoundIndex != mtf_queue_number)                                                  \
      RangeLow += FreqMtfQueueNum[Context][FoundIndex++];                                   \
    low += RangeLow * (range /= RangeScaleMtfQueueNum[Context]);                            \
    range *= FreqMtfQueueNum[Context][FoundIndex];                                          \
  }                                                                                         \
}
#define UpFreqMtfQueueNum(Context) {                                                         \
  FreqMtfQueueNum[Context][mtf_queue_number] += UP_FREQ_MTF_QUEUE_NUM2;                      \
  if ((RangeScaleMtfQueueNum[Context] += UP_FREQ_MTF_QUEUE_NUM2) >= FREQ_MTF_QUEUE_NUM_BOT)  \
    rescaleMtfQueueNum(Context);                                                             \
}
#define UpFreqMtfQueueNumD(Context) {                                                        \
  FreqMtfQueueNum[Context][mtf_queue_number] += UP_FREQ_MTF_QUEUE_NUM2;                      \
  if ((RangeScaleMtfQueueNum[Context] += UP_FREQ_MTF_QUEUE_NUM2) >= FREQ_MTF_QUEUE_NUM_BOT)  \
    rescaleMtfQueueNum(Context);                                                             \
}
#define UpFreqMtfQueueNumHitD(Context) {                                                     \
  FreqMtfQueueNum[Context][mtf_queue_number] += UP_FREQ_MTF_QUEUE_NUM;                       \
  if ((RangeScaleMtfQueueNum[Context] += UP_FREQ_MTF_QUEUE_NUM) >= FREQ_MTF_QUEUE_NUM_BOT)   \
    rescaleMtfQueueNum(Context);                                                             \
}
#define EncodeMtfQueuePos(Context) {                                                                                     \
  NormalizeEncoder(FREQ_MTF_QUEUE_POS_BOT);                                                                              \
  if (mtf_queue_position == 0) {                                                                                         \
    range = FreqMtfQueuePos[Context][mtf_queue_number][0] * (range / RangeScaleMtfQueuePos[Context][mtf_queue_number]);  \
    FreqMtfQueuePos[Context][mtf_queue_number][0] += UP_FREQ_MTF_QUEUE_POS;                                              \
  }                                                                                                                      \
  else {                                                                                                                 \
    RangeLow = FreqMtfQueuePos[Context][mtf_queue_number][0];                                                            \
    FoundIndex = 1;                                                                                                      \
    while (FoundIndex != mtf_queue_position)                                                                             \
      RangeLow += FreqMtfQueuePos[Context][mtf_queue_number][FoundIndex++];                                              \
    low += RangeLow * (range /= RangeScaleMtfQueuePos[Context][mtf_queue_number]);                                       \
    range *= FreqMtfQueuePos[Context][mtf_queue_number][FoundIndex];                                                     \
    FreqMtfQueuePos[Context][mtf_queue_number][FoundIndex] += UP_FREQ_MTF_QUEUE_POS;                                     \
  }                                                                                                                      \
  if ((RangeScaleMtfQueuePos[Context][mtf_queue_number] += UP_FREQ_MTF_QUEUE_POS) >= FREQ_MTF_QUEUE_POS_BOT)             \
    rescaleMtfQueuePos(Context);                                                                                         \
}
#define EncodeMtfgQueuePos(Context) {                                                          \
  NormalizeEncoder(FREQ_MTFG_QUEUE_POS_BOT);                                                   \
  if (mtfg_queue_position == 0) {                                                              \
    range = FreqMtfgQueuePos[Context][0] * (range / RangeScaleMtfgQueuePos[Context]);          \
    FreqMtfgQueuePos[Context][0] += UP_FREQ_MTFG_QUEUE_POS;                                    \
  }                                                                                            \
  else {                                                                                       \
    RangeLow = FreqMtfgQueuePos[Context][0];                                                   \
    FoundIndex = 1;                                                                            \
    while (FoundIndex != mtfg_queue_position)                                                  \
      RangeLow += FreqMtfgQueuePos[Context][FoundIndex++];                                     \
    low += RangeLow * (range /= RangeScaleMtfgQueuePos[Context]);                              \
    range *= FreqMtfgQueuePos[Context][FoundIndex];                                            \
    FreqMtfgQueuePos[Context][FoundIndex] += UP_FREQ_MTFG_QUEUE_POS;                           \
  }                                                                                            \
  if ((RangeScaleMtfgQueuePos[Context] += UP_FREQ_MTFG_QUEUE_POS) >= FREQ_MTFG_QUEUE_POS_BOT)  \
    rescaleMtfgQueuePos(Context);                                                              \
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
  if ((RangeScaleSID[Context] += UP_FREQ_SID) >= FREQ_SID_BOT)       \
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
  if ((RangeScaleINST[Context][SIDSymbol] += UP_FREQ_INST) >= FREQ_INST_BOT)                 \
    rescaleINST(Context);                                                                    \
}
#define EncodeERG(Symbol) {                            \
  NormalizeEncoder(FREQ_ERG_BOT);                      \
  if (Symbol == 0) {                                   \
    range = FreqERG0 * (range / RangeScaleERG);        \
    FreqERG0 += UP_FREQ_ERG;                           \
  }                                                    \
  else {                                               \
    low += FreqERG0 * (range /= RangeScaleERG);        \
    range *= RangeScaleERG - FreqERG0;                 \
  }                                                    \
  if ((RangeScaleERG += UP_FREQ_ERG) >= FREQ_ERG_BOT)  \
      rescaleERG();                                    \
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
#define EncodeFirstChar(LastChar) {                                                       \
  NormalizeEncoder(FREQ_FIRST_CHAR_BOT);                                                  \
  if (Symbol == SymbolFirstChar[LastChar][0]) {                                           \
    range = FreqFirstChar[LastChar][0] * (range / RangeScaleFirstChar[LastChar]);         \
    FreqFirstChar[LastChar][0] += UP_FREQ_FIRST_CHAR;                                     \
  }                                                                                       \
  else {                                                                                  \
    RangeLow = FreqFirstChar[LastChar][0];                                                \
    FoundIndex = 1;                                                                       \
    while (SymbolFirstChar[LastChar][FoundIndex] != Symbol)                               \
      RangeLow += FreqFirstChar[LastChar][FoundIndex++];                                  \
    low += RangeLow * (range /= RangeScaleFirstChar[LastChar]);                           \
    range *= FreqFirstChar[LastChar][FoundIndex];                                         \
    FreqFirstChar[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;                            \
    if (FreqFirstChar[LastChar][FoundIndex] > FreqFirstChar[LastChar][FoundIndex-1]) {    \
      unsigned short int SavedFreq = FreqFirstChar[LastChar][FoundIndex];                 \
      do {                                                                                \
        FreqFirstChar[LastChar][FoundIndex] = FreqFirstChar[LastChar][FoundIndex-1];      \
        SymbolFirstChar[LastChar][FoundIndex] = SymbolFirstChar[LastChar][FoundIndex-1];  \
      } while ((--FoundIndex) && (SavedFreq > FreqFirstChar[LastChar][FoundIndex-1]));    \
      FreqFirstChar[LastChar][FoundIndex] = SavedFreq;                                    \
      SymbolFirstChar[LastChar][FoundIndex] = Symbol;                                     \
    }                                                                                     \
  }                                                                                       \
  if ((RangeScaleFirstChar[LastChar] += UP_FREQ_FIRST_CHAR) > FREQ_FIRST_CHAR_BOT)        \
    rescaleFirstChar(LastChar);                                                           \
}
void InitEncoder(FILE* EncodedFile) {
  OutFile = EncodedFile;
  OutCharNum = 0;
  low = 0, range = -1;
  if (use_mtf) {
    StartModelSymType();
  }
  else {
    StartModelSymTypeNoMtf();
  }
  StartModelMtfQueueNum();
  StartModelMtfQueuePos();
  StartModelMtfgQueuePos();
  StartModelSID();
  StartModelINST();
  StartModelERG();
  StartModelFirstChar();
}
void FinishEncoder() {
  while (low ^ (low + range)) {
    WriteByte(low >> 24, OutFile);
    low <<= 8;
    range <<= 8;
  }
  fwrite(OutData,1,OutCharNum,OutFile);
}
#define NormalizeDecoder(bot) {                                                                \
  while ((low ^ (low + range)) < TOP || range < (bot) && ((range = -low & ((bot) - 1)), 1)) {  \
    ReadByte(InFile);                                                                          \
    code = (code << 8) | Symbol;                                                               \
    low <<= 8;                                                                                 \
    range <<= 8;                                                                               \
  }                                                                                            \
}
#define DecodeSymType(Context) {                                                       \
  NormalizeDecoder(FREQ_SYM_TYPE_BOT);                                                 \
  count = (code - low) / (range /= RangeScaleSymType[Context]);                        \
  if (FreqSymType[Context][0] > count) {                                               \
    range *= FreqSymType[Context][0];                                                  \
    FreqSymType[Context][0] += UP_FREQ_SYM_TYPE;                                       \
    Symbol = 0;                                                                        \
  }                                                                                    \
  else if ((RangeHigh = FreqSymType[Context][0] + FreqSymType[Context][1]) > count) {  \
    low += range * FreqSymType[Context][0];                                            \
    range *= FreqSymType[Context][1];                                                  \
    FreqSymType[Context][1] += UP_FREQ_SYM_TYPE;                                       \
    Symbol = 1;                                                                        \
  }                                                                                    \
  else if ((RangeHigh + FreqSymType[Context][2]) > count) {                            \
    low += range * RangeHigh;                                                          \
    range *= FreqSymType[Context][2];                                                  \
    FreqSymType[Context][2] += UP_FREQ_SYM_TYPE;                                       \
    Symbol = 2;                                                                        \
  }                                                                                    \
  else {                                                                               \
    low += range * (RangeHigh + FreqSymType[Context][2]);                              \
    range *= FreqSymType[Context][3];                                                  \
    FreqSymType[Context][3] += UP_FREQ_SYM_TYPE;                                       \
    Symbol = 3;                                                                        \
  }                                                                                    \
  if ((RangeScaleSymType[Context] += UP_FREQ_SYM_TYPE) >= FREQ_SYM_TYPE_BOT)           \
    rescaleSymType(Context);                                                           \
}
#define DecodeMtfQueueNum(Context) {                                            \
  NormalizeDecoder(FREQ_MTF_QUEUE_NUM_BOT);                                     \
  count = (code - low) / (range /= RangeScaleMtfQueueNum[Context]);             \
  if ((RangeHigh = FreqMtfQueueNum[Context][0]) > count) {                      \
    range *= RangeHigh;                                                         \
    mtf_queue_number = 0;                                                       \
  }                                                                             \
  else {                                                                        \
    mtf_queue_number = 1;                                                       \
    while ((RangeHigh += FreqMtfQueueNum[Context][mtf_queue_number]) <= count)  \
      mtf_queue_number++;                                                       \
    low += range * (RangeHigh - FreqMtfQueueNum[Context][mtf_queue_number]);    \
    range *= FreqMtfQueueNum[Context][mtf_queue_number];                        \
  }                                                                             \
}
#define DecodeMtfQueuePos(Context) {                                                                          \
  NormalizeDecoder(FREQ_MTF_QUEUE_POS_BOT);                                                                   \
  count = (code - low) / (range /= RangeScaleMtfQueuePos[Context][mtf_queue_number]);                         \
  if ((RangeHigh = FreqMtfQueuePos[Context][mtf_queue_number][0]) > count) {                                  \
    range *= RangeHigh;                                                                                       \
    FreqMtfQueuePos[Context][mtf_queue_number][0] = RangeHigh + UP_FREQ_MTF_QUEUE_POS;                        \
    Symbol = 0;                                                                                               \
  }                                                                                                           \
  else {                                                                                                      \
    Symbol = 1;                                                                                               \
    while ((RangeHigh += FreqMtfQueuePos[Context][mtf_queue_number][Symbol]) <= count)                        \
      Symbol++;                                                                                               \
    low += range * (RangeHigh - FreqMtfQueuePos[Context][mtf_queue_number][Symbol]);                          \
    range *= FreqMtfQueuePos[Context][mtf_queue_number][Symbol];                                              \
    FreqMtfQueuePos[Context][mtf_queue_number][Symbol] += UP_FREQ_MTF_QUEUE_POS;                              \
  }                                                                                                           \
  if ((RangeScaleMtfQueuePos[Context][mtf_queue_number] += UP_FREQ_MTF_QUEUE_POS) >= FREQ_MTF_QUEUE_POS_BOT)  \
    rescaleMtfQueuePos(Context);                                                                              \
}
#define DecodeMtfgQueuePos(Context) {                                                          \
  NormalizeDecoder(FREQ_MTFG_QUEUE_POS_BOT);                                                   \
  count = (code - low) / (range /= RangeScaleMtfgQueuePos[Context]);                           \
  if ((RangeHigh = FreqMtfgQueuePos[Context][0]) > count) {                                    \
    range *= RangeHigh;                                                                        \
    FreqMtfgQueuePos[Context][0] = RangeHigh + UP_FREQ_MTFG_QUEUE_POS;                         \
    mtfg_queue_position = 0;                                                                   \
  }                                                                                            \
  else {                                                                                       \
    mtfg_queue_position = 1;                                                                   \
    while ((RangeHigh += FreqMtfgQueuePos[Context][mtfg_queue_position]) <= count)             \
      mtfg_queue_position++;                                                                   \
    low += range * (RangeHigh - FreqMtfgQueuePos[Context][mtfg_queue_position]);               \
    range *= FreqMtfgQueuePos[Context][mtfg_queue_position];                                   \
    FreqMtfgQueuePos[Context][mtfg_queue_position] += UP_FREQ_MTFG_QUEUE_POS;                  \
  }                                                                                            \
  if ((RangeScaleMtfgQueuePos[Context] += UP_FREQ_MTFG_QUEUE_POS) >= FREQ_MTFG_QUEUE_POS_BOT)  \
    rescaleMtfgQueuePos(Context);                                                              \
}
#define DecodeSID(Context) {                                     \
  NormalizeDecoder(FREQ_SID_BOT);                                \
  count = (code - low) / (range /= RangeScaleSID[Context]);      \
  if ((RangeHigh = FreqSID[Context][0]) > count) {               \
    range *= RangeHigh;                                          \
    FreqSID[Context][0] = RangeHigh + UP_FREQ_SID;               \
    SIDSymbol = 0;                                               \
  }                                                              \
  else {                                                         \
    SIDSymbol = 1;                                               \
    while ((RangeHigh += FreqSID[Context][SIDSymbol]) <= count)  \
      SIDSymbol++;                                               \
    low += range * (RangeHigh - FreqSID[Context][SIDSymbol]);    \
    range *= FreqSID[Context][SIDSymbol];                        \
    FreqSID[Context][SIDSymbol] += UP_FREQ_SID;                  \
  }                                                              \
  if ((RangeScaleSID[Context] += UP_FREQ_SID) >= FREQ_SID_BOT)   \
    rescaleSID(Context);                                         \
}
#define DecodeExtraLength() {             \
  NormalizeDecoder(1 << 2);               \
  Symbol = (code - low) / (range >>= 2);  \
  low += range * Symbol;                  \
}
#define DecodeINST(Context) {                                                 \
  NormalizeDecoder(FREQ_INST_BOT);                                            \
  count = (code - low) / (range /= RangeScaleINST[Context][SIDSymbol]);       \
  if ((RangeHigh = FreqINST[Context][SIDSymbol][0]) > count) {                \
    range *= RangeHigh;                                                       \
    FreqINST[Context][SIDSymbol][0] = RangeHigh + UP_FREQ_INST;               \
    Instances = 0;                                                            \
  }                                                                           \
  else {                                                                      \
    Instances = 1;                                                            \
    while ((RangeHigh += FreqINST[Context][SIDSymbol][Instances]) <= count)   \
      Instances++;                                                            \
    low += range * (RangeHigh - FreqINST[Context][SIDSymbol][Instances]);     \
    range *= FreqINST[Context][SIDSymbol][Instances];                         \
    FreqINST[Context][SIDSymbol][Instances] += UP_FREQ_INST;                  \
  }                                                                           \
  if ((RangeScaleINST[Context][SIDSymbol] += UP_FREQ_INST) >= FREQ_INST_BOT)  \
    rescaleINST(Context);                                                     \
}
#define DecodeERG() {                                  \
  NormalizeDecoder(FREQ_ERG_BOT);                      \
  count = (code - low) / (range /= RangeScaleERG);     \
  if (FreqERG0 > count) {                              \
    range *= FreqERG0;                                 \
    FreqERG0 += UP_FREQ_ERG;                           \
    nonergodic = 0;                                    \
  }                                                    \
  else {                                               \
    low += range * FreqERG0;                           \
    range *= RangeScaleERG - FreqERG0;                 \
    nonergodic = 1;                                    \
  }                                                    \
  if ((RangeScaleERG += UP_FREQ_ERG) >= FREQ_ERG_BOT)  \
    rescaleERG();                                      \
}
#define DecodeDictionaryBin(lookup_bits) {                                      \
  NormalizeDecoder(1 << 12);                                                    \
  CodeLength = lookup_bits[BinNum = (code - low) / (range /= DictionaryBins)];  \
  char BitsUnderBinSize = 12 + nbob_shift[FirstChar] - CodeLength;              \
  if (BitsUnderBinSize >= 0)                                                    \
    low += (range <<= BitsUnderBinSize) * (BinNum >> BitsUnderBinSize);         \
  else                                                                          \
    low += range * BinNum;                                                      \
}
#define DecodeDictionarySymbolIndex(Bits,FirstBin,SymbolArray) {             \
  NormalizeDecoder(1 << Bits);                                               \
  BinCode = (code - low) / (range >>= Bits);                                 \
  SymbolIndex = (1 << Bits) * (BinNum - FirstBin) + BinCode;                 \
  if (SymbolIndex >= min_extra_reduce_index) {                               \
    BinCode &= -2;                                                           \
    SymbolIndex = (SymbolIndex + min_extra_reduce_index) >> 1;               \
    unsigned int index = SymbolIndex;                                        \
    unsigned int extra_code_bins = 0;                                        \
    while (BinCode && (symbol_type[SymbolArray[--index]] & 8)) {             \
      char bins = (index >= min_extra_reduce_index) ? 2 : 1;                 \
      BinCode -= bins;                                                       \
      extra_code_bins += bins;                                               \
    }                                                                        \
    low += range * BinCode;                                                  \
    while (symbol_type[SymbolArray[SymbolIndex]] & 8) {                      \
      SymbolIndex++;                                                         \
      extra_code_bins += 2;                                                  \
    }                                                                        \
    range *= 2 + extra_code_bins;                                            \
  }                                                                          \
  else {                                                                     \
    unsigned int index = SymbolIndex;                                        \
    unsigned int extra_code_bins = 0;                                        \
    while (BinCode && (symbol_type[SymbolArray[--index]] & 8)) {             \
      BinCode--;                                                             \
      extra_code_bins++;                                                     \
    }                                                                        \
    low += range * BinCode;                                                  \
    while (symbol_type[SymbolArray[SymbolIndex]] & 8)                        \
      extra_code_bins += (++SymbolIndex >= min_extra_reduce_index) ? 2 : 1;  \
    range *= 1 + extra_code_bins;                                            \
  }                                                                          \
}
#define DecodeBaseSymbol(Bits) {                                  \
  NormalizeDecoder(1 << Bits);                                    \
  low += range * (BaseSymbol = (code - low) / (range >>= Bits));  \
}
#define DecodeFirstChar(LastChar) {                                                       \
  NormalizeDecoder(FREQ_FIRST_CHAR_BOT);                                                  \
  count = (code - low) / (range /= RangeScaleFirstChar[LastChar]);                        \
  if ((RangeHigh = FreqFirstChar[LastChar][0]) > count) {                                 \
    range *= RangeHigh;                                                                   \
    FreqFirstChar[LastChar][0] = RangeHigh + UP_FREQ_FIRST_CHAR;                          \
    FirstChar = SymbolFirstChar[LastChar][0];                                             \
  }                                                                                       \
  else {                                                                                  \
    FoundIndex = 1;                                                                       \
    while ((RangeHigh += FreqFirstChar[LastChar][FoundIndex]) <= count)                   \
      FoundIndex++;                                                                       \
    low += range * (RangeHigh - FreqFirstChar[LastChar][FoundIndex]);                     \
    range *= FreqFirstChar[LastChar][FoundIndex];                                         \
    FreqFirstChar[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;                            \
    FirstChar = SymbolFirstChar[LastChar][FoundIndex];                                    \
    if (FreqFirstChar[LastChar][FoundIndex] > FreqFirstChar[LastChar][FoundIndex-1]) {    \
      unsigned short int SavedFreq = FreqFirstChar[LastChar][FoundIndex];                 \
      do {                                                                                \
        FreqFirstChar[LastChar][FoundIndex] = FreqFirstChar[LastChar][FoundIndex-1];      \
        SymbolFirstChar[LastChar][FoundIndex] = SymbolFirstChar[LastChar][FoundIndex-1];  \
      } while ((--FoundIndex) && (SavedFreq > FreqFirstChar[LastChar][FoundIndex-1]));    \
      FreqFirstChar[LastChar][FoundIndex] = SavedFreq;                                    \
      SymbolFirstChar[LastChar][FoundIndex] = FirstChar;                                  \
    }                                                                                     \
  }                                                                                       \
  if ((RangeScaleFirstChar[LastChar] += UP_FREQ_FIRST_CHAR) > FREQ_FIRST_CHAR_BOT)        \
    rescaleFirstChar(LastChar);                                                           \
}
void InitDecoder(FILE* EncodedFile) {
  InFile = EncodedFile;
  NumInChar = 0, InCharNum = 0, OutCharNum = 0;
  code = 0, range = -1;
  for (low = 4; low != 0; low--) {
    ReadByte(InFile);
    code = (code << 8) | Symbol;
  }
  if (use_mtf) {
    StartModelSymType();
  }
  else {
    StartModelSymTypeNoMtf();
  }
  StartModelMtfQueueNum();
  StartModelMtfQueuePos();
  StartModelMtfgQueuePos();
  StartModelSID();
  StartModelINST();
  StartModelERG();
  StartModelFirstChar();
}

