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

// GLZAcompress.c
//   Iteratively does the following until there are no symbols worth generating:
//     1. Counts the symbol occurances in the input data and calculates the log base 2 of each symbol's probability of occuring
//     2. Builds portions of the generalized suffix tree and searches them for the "most compressible" symbol strings
//     3. Invalidates less desireable strings that overlap with better ones
//     4. Replaces each occurence of the best strings with a new symbol and adds the best strings to the end of the file
//        with a unique (define) symbol marker at the start of the string
//
// Usage:
//   GLZAcompress [-m#] [-p#] [-r#] <infilename> <outfilename>, where
//       -m# sets the production cost, default 6.0
//       -p# sets the profit ratio weighting power, default 2.0 (must be >= 0.0)
//       -r# sets the approximate RAM usage / input file size ratio (default 6.5 for UTF-8 compliant
//           files, 10.5 for non UTF-8 compliant files, minimum is 5.0)

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <pthread.h>
#include "GLZA.h"

const U8 INSERT_SYMBOL_CHAR = 0xFE;
const U8 DEFINE_SYMBOL_CHAR = 0xFF;
const U32 START_MY_SYMBOLS = 0x00080000;
const U32 MAX_WRITE_SIZE = 0x200000;
const U32 MAX_PRIOR_MATCHES = 20;
const U32 MAX_STRING_LENGTH = 8000;
const U32 BASE_NODES_CHILD_ARRAY_SIZE = 16;
const U32 NUM_PRECALCULATED_INSTANCE_LOGS = 10000;
const U32 NUM_PRECALCULATED_MATCH_RATIO_LOGS = 2000;
const U32 MAX_SCORES = 30000;

static struct string_node {
  U32 symbol;
  U32 last_match_index;
  U32 sibling_node_num[4];
  U32 instances;
  U32 child_node_num;
} *string_nodes;

static struct match_node {
  U32 symbol;
  U32 num_symbols;
  U32 score_number;
  struct match_node *child_ptr;
  U32 sibling_node_num[16];
  struct match_node *miss_ptr;
  struct match_node *hit_ptr;
} *match_nodes, *match_node_ptr, *child_match_node_ptr, *search_node_ptr;

struct node_score_data {
  U32 last_match_index1;
  U32 last_match_index2;
  float score;
  U16 num_symbols;
} node_scores[30000];

struct lcp_thread_data {
  U32 min_symbol;
  U32 max_symbol;
  U32 string_nodes_limit;
  U32 first_string_node_num;
  U32 *current_symbol_ptr;
} lcp_thread_data[12];

struct rank_scores_struct {
  double score;
  volatile size_t node_ptrs;
  U16 node_num_symbols;
} rank_scores_buffer[0x10000];

struct score_data {
  struct string_node *node_ptr;
  double string_entropy;
  U16 num_symbols_in_string;
  U8 next_sibling;
} node_data[20000];

struct overlap_check_data {
  U32 *start_symbol_ptr;
  U32 *stop_symbol_ptr;
} overlap_check_data[7];

struct find_substitutions_data {
  U32 *stop_symbol_ptr;
  U32 extra_match_symbols;
  volatile U32 *start_symbol_ptr;
  volatile U32 num_substitutions;
  volatile U32 data[0x400000];
  volatile U8 done;
} find_substitutions_data[6];

U32 this_symbol, max_string_length, max_scores, i1;
U32 num_simple_symbols, node_instances, num_match_nodes, best_score_num_symbols, sibling_node_number;
U32 new_symbol_number[30000];
U32 symbol_count[10000000];
U32 *start_symbol_ptr, *end_symbol_ptr, *in_symbol_ptr, *out_symbol_ptr, *min_symbol_ptr;
U32 *base_string_nodes_child_node_num, *best_score_last_match_ptr, *node_last_match_ptr;
U32 * volatile max_symbol_ptr;
U32 * volatile stop_symbol_ptr;
volatile U32 substitute_data[0x10000];
U16 node_ptrs_num, num_node_scores, node_scores_index[30000];
U8 node_scores_bad[30000];
U8 *char_buffer, *in_char_ptr, *end_char_ptr;
double log2_num_symbols_plus_substitution_cost, min_score, production_cost, profit_ratio_power;
double new_symbol_cost[2000], log2_instances[10000];
double *symbol_entropy;



static inline U32* init_best_score_ptrs()
{
  best_score_last_match_ptr = node_scores[node_scores_index[i1]].last_match_index1 + start_symbol_ptr;
  return(best_score_last_match_ptr - node_scores[node_scores_index[i1]].num_symbols + 1);
}



#define init_match_node(match_num_symbols, match_score_number) \
{ \
  match_node_ptr->symbol = this_symbol; \
  match_node_ptr->num_symbols = match_num_symbols; \
  match_node_ptr->score_number = match_score_number; \
  match_node_ptr->child_ptr = 0; \
  U64 * sibling_nodes_ptr; \
  sibling_nodes_ptr = (U64 *)&match_node_ptr->sibling_node_num[0]; \
  *sibling_nodes_ptr = 0; \
  *(sibling_nodes_ptr+1) = 0; \
  *(sibling_nodes_ptr+2) = 0; \
  *(sibling_nodes_ptr+3) = 0; \
  *(sibling_nodes_ptr+4) = 0; \
  *(sibling_nodes_ptr+5) = 0; \
  *(sibling_nodes_ptr+6) = 0; \
  *(sibling_nodes_ptr+7) = 0; \
  match_node_ptr->miss_ptr = 0; \
  match_node_ptr->hit_ptr = 0; \
}



#define init_level_1_match_node(match_symbol, match_score_number) \
{ \
  match_node_ptr->symbol = match_symbol; \
  match_node_ptr->num_symbols = 1; \
  match_node_ptr->score_number = match_score_number; \
  match_node_ptr->child_ptr = 0; \
  U64 *sibling_nodes_ptr; \
  sibling_nodes_ptr = (U64 *)&match_node_ptr->sibling_node_num[0]; \
  *sibling_nodes_ptr = 0; \
  *(sibling_nodes_ptr+1) = 0; \
  *(sibling_nodes_ptr+2) = 0; \
  *(sibling_nodes_ptr+3) = 0; \
  *(sibling_nodes_ptr+4) = 0; \
  *(sibling_nodes_ptr+5) = 0; \
  *(sibling_nodes_ptr+6) = 0; \
  *(sibling_nodes_ptr+7) = 0; \
  match_node_ptr->miss_ptr = 0; \
  match_node_ptr->hit_ptr = 0; \
}



#define move_to_match_sibling(match_node_ptr, sibling_number) \
{ \
  U32 shifted_symbol = this_symbol; \
  sibling_number = (U8)(shifted_symbol & 0xF); \
  while ((this_symbol != match_node_ptr->symbol) && (match_node_ptr->sibling_node_num[sibling_number] != 0)) { \
    match_node_ptr = &match_nodes[match_node_ptr->sibling_node_num[sibling_number]]; \
    shifted_symbol = shifted_symbol >> 4; \
    sibling_number = (U8)(shifted_symbol & 0xF); \
  } \
}



#define move_to_match_child(match_node_ptr, sibling_number) \
{ \
  match_node_ptr = match_node_ptr->child_ptr; \
  move_to_match_sibling(match_node_ptr, sibling_number); \
}



#define move_to_existing_match_sibling() \
{ \
  U32 shifted_symbol = this_symbol; \
  U8 sibling_number = (U8)(shifted_symbol & 0xF); \
  while (this_symbol != match_node_ptr->symbol) { \
    match_node_ptr = &match_nodes[match_node_ptr->sibling_node_num[sibling_number]]; \
    shifted_symbol = shifted_symbol >> 4; \
    sibling_number = (U8)(shifted_symbol & 0xF); \
  } \
}



#define move_to_existing_match_child() \
{ \
  match_node_ptr = match_node_ptr->child_ptr; \
  move_to_existing_match_sibling(); \
}



static inline void move_to_search_sibling()
{
  U8 sibling_nibble, sibling_depth;
  U32 shifted_symbol;

  sibling_depth = 0;
  shifted_symbol = this_symbol;
  sibling_nibble = (U8)(shifted_symbol & 0xF);
  while ((this_symbol != search_node_ptr->symbol) && (search_node_ptr->sibling_node_num[sibling_nibble] != 0)) {
    search_node_ptr = &match_nodes[search_node_ptr->sibling_node_num[sibling_nibble]];
    sibling_depth++;
    shifted_symbol = shifted_symbol >> 4;
    sibling_nibble = (U8)(shifted_symbol & 0xF);
  }
  return;
}



static inline void move_to_search_child()
{
  search_node_ptr = search_node_ptr->child_ptr;
  move_to_search_sibling();
  return;
}



#define make_and_move_to_match_child() \
{ \
  match_node_ptr->child_ptr = &match_nodes[num_match_nodes++]; \
  match_node_ptr = match_node_ptr->child_ptr; \
  init_match_node(best_score_num_symbols,i1); \
}



static inline void make_and_move_to_match_sibling(U32 num_symbols, U32 score_number, U8 sibling_number)
{
  match_node_ptr->sibling_node_num[sibling_number] = num_match_nodes;
  match_node_ptr = &match_nodes[num_match_nodes++];
  init_match_node(num_symbols,score_number);
  return;
}



static inline void move_to_match_child_with_make()
{
  if (match_node_ptr->child_ptr == 0) {
    make_and_move_to_match_child();
  }
  else {
    match_node_ptr = match_node_ptr->child_ptr;
    U8 sibling_number;
    move_to_match_sibling(match_node_ptr,sibling_number);
    if (this_symbol != match_node_ptr->symbol)
      make_and_move_to_match_sibling(best_score_num_symbols,i1,sibling_number);
  }
  return;
}



static inline void write_siblings_miss_ptr(struct match_node *child_ptr)
{
  U8 sibling_nibble;
  child_ptr->miss_ptr = search_node_ptr->child_ptr;
  for (sibling_nibble=0 ; sibling_nibble<16 ; sibling_nibble++) {
    sibling_node_number = child_ptr->sibling_node_num[sibling_nibble];
    if (sibling_node_number != 0)
      write_siblings_miss_ptr(&match_nodes[sibling_node_number]);
  }
  return;
}



static inline void write_all_children_miss_ptr()
{
  U8 sibling_nibble;
  child_match_node_ptr = match_node_ptr->child_ptr;
  if (child_match_node_ptr->miss_ptr == 0) {
    child_match_node_ptr->miss_ptr = search_node_ptr->child_ptr;
    for (sibling_nibble=0 ; sibling_nibble<16 ; sibling_nibble++) {
      sibling_node_number = child_match_node_ptr->sibling_node_num[sibling_nibble];
      if (sibling_node_number != 0)
        write_siblings_miss_ptr(&match_nodes[sibling_node_number]);
    }
  }
  return;
}



static inline void add_suffix(U32 this_symbol, U32 *in_symbol_ptr, U32 *next_string_node_num_ptr)
{
  U32 search_symbol, match_start_index;
  U32 *base_node_child_num_ptr, *node_data_ptr;
  struct string_node *child_ptr, *next_child_ptr;
  search_symbol = *in_symbol_ptr;
  base_node_child_num_ptr = &base_string_nodes_child_node_num[this_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 0xF)];
  if (*base_node_child_num_ptr) {
    U32 shifted_search_symbol;
    match_start_index = in_symbol_ptr - start_symbol_ptr - 1;
    child_ptr = &string_nodes[*base_node_child_num_ptr];
    if ((int)search_symbol >= 0) {
      shifted_search_symbol = search_symbol >> 4;
      while (search_symbol != child_ptr->symbol) { // follow siblings until match found or end of siblings found
        U32 *next_child_node_num_ptr;
        next_child_node_num_ptr = (U32 *)&child_ptr->sibling_node_num[shifted_search_symbol & 3];
        next_child_ptr = &string_nodes[*next_child_node_num_ptr];
        if (next_child_ptr != string_nodes) {
          child_ptr = next_child_ptr;
          shifted_search_symbol = shifted_search_symbol >> 2;
        }
        else { // no matching child so add sibling
          node_data_ptr = (U32 *)&string_nodes[*next_string_node_num_ptr];
          *node_data_ptr = *in_symbol_ptr;
          *(node_data_ptr+1) = (U32)(in_symbol_ptr - start_symbol_ptr);
          *((U64 *)node_data_ptr+1) = 0;
          *((U64 *)node_data_ptr+2) = 0;
          *((U64 *)node_data_ptr+3) = 1;
          *next_child_node_num_ptr = *next_string_node_num_ptr;
          *next_string_node_num_ptr += 1;
          return;
        }
      }
      // found a matching sibling
      if (child_ptr->child_node_num == 0) {
        // matching child without grandchild so create grandchild for previous instance then add string to grandchild
        node_data_ptr = (U32 *)&string_nodes[*next_string_node_num_ptr];
        *node_data_ptr = *(start_symbol_ptr + child_ptr->last_match_index + 1);
        *(node_data_ptr+1) = child_ptr->last_match_index + 1;
        *((U64 *)node_data_ptr+1) = 0;
        *((U64 *)node_data_ptr+2) = 0;
        *((U64 *)node_data_ptr+3) = 1;
        child_ptr->child_node_num = *next_string_node_num_ptr;
        *next_string_node_num_ptr += 1;
      }
      if (match_start_index > child_ptr->last_match_index) {
        // increment instances and update last_match_index for strings that do not overlap
        child_ptr->instances++;
        child_ptr->last_match_index = (U32)(in_symbol_ptr - start_symbol_ptr);
      }
      child_ptr = &string_nodes[child_ptr->child_node_num];

      U32 *next_child_node_num_ptr, *match_max_ptr;
      match_max_ptr = start_symbol_ptr + match_start_index + MAX_STRING_LENGTH;
      search_symbol = *++in_symbol_ptr;
      if (search_symbol != child_ptr->symbol) { // go to sibling and check for end of siblings
        if ((int)search_symbol < 0)
          return;
add_string_to_child_not_match:
        next_child_node_num_ptr = (U32 *)&child_ptr->sibling_node_num[search_symbol & 3];
        if (*next_child_node_num_ptr == 0)
          goto add_string_to_child_add_sibling;
        child_ptr = &string_nodes[*next_child_node_num_ptr];
        if (search_symbol != child_ptr->symbol) {
          shifted_search_symbol = search_symbol >> 2;
add_string_to_child_check_sibling:
          next_child_node_num_ptr = (U32 *)&child_ptr->sibling_node_num[shifted_search_symbol & 3];
          if (*next_child_node_num_ptr) {
            child_ptr = &string_nodes[*next_child_node_num_ptr];
            if (search_symbol == child_ptr->symbol)
              goto add_string_to_child_match;
            shifted_search_symbol = shifted_search_symbol >> 2;
            goto add_string_to_child_check_sibling;
          }
          else { // no matching child so add sibling
add_string_to_child_add_sibling:
            node_data_ptr = (U32 *)&string_nodes[*next_string_node_num_ptr];
            *node_data_ptr = *in_symbol_ptr;
            *(node_data_ptr+1) = (U32)(in_symbol_ptr - start_symbol_ptr);
            *((U64 *)node_data_ptr+1) = 0;
            *((U64 *)node_data_ptr+2) = 0;
            *((U64 *)node_data_ptr+3) = 1;
            *next_child_node_num_ptr = *next_string_node_num_ptr;
            *next_string_node_num_ptr += 1;
            return;
          }
        }
      }
add_string_to_child_match:
      // found a matching sibling
      if (child_ptr->child_node_num == 0) {
        // matching child without grandchild so create grandchild for previous instance then add string to grandchild
        if (in_symbol_ptr >= match_max_ptr)
          return;
        node_data_ptr = (U32 *)&string_nodes[*next_string_node_num_ptr];
        *node_data_ptr = *(start_symbol_ptr + (size_t)child_ptr->last_match_index + 1);
        *(node_data_ptr+1) = child_ptr->last_match_index + 1;
        *((U64 *)node_data_ptr+1) = 0;
        *((U64 *)node_data_ptr+2) = 0;
        *((U64 *)node_data_ptr+3) = 1;
        child_ptr->child_node_num = *next_string_node_num_ptr;
        *next_string_node_num_ptr += 1;
      }
      if (match_start_index > child_ptr->last_match_index) {
        // increment instances and update last_match_index for strings that do not overlap
        child_ptr->instances++;
        child_ptr->last_match_index = (U32)(in_symbol_ptr - start_symbol_ptr);
      }
      child_ptr = &string_nodes[child_ptr->child_node_num];
      search_symbol = *++in_symbol_ptr;
      if (search_symbol == child_ptr->symbol)
        goto add_string_to_child_match;
      if ((int)search_symbol >= 0)
        goto add_string_to_child_not_match;
      return;
    }
  }
  else { // first occurence of the symbol, so create a child
    node_data_ptr = (U32 *)&string_nodes[*next_string_node_num_ptr];
    *node_data_ptr = search_symbol;
    *(node_data_ptr+1) = (U32)(in_symbol_ptr - start_symbol_ptr);
    *((U64 *)node_data_ptr+1) = 0;
    *((U64 *)node_data_ptr+2) = 0;
    *((U64 *)node_data_ptr+3) = 1;
    *base_node_child_num_ptr = *next_string_node_num_ptr;
    *next_string_node_num_ptr += 1;
  }
  return;
}



void *rank_scores_thread(void *arg)
{
  struct string_node *node_ptr, *next_child_ptr;
  double d_score;
  float score;
  U32 *node_last_match_ptr;
  U16 num_symbols_in_string, score_index, node_score_num_symbols;
  U16 node_ptrs_num = 0;

  do {
    node_ptr = (struct string_node *)rank_scores_buffer[node_ptrs_num].node_ptrs;
    if ((size_t)node_ptr > 1) {
      d_score = rank_scores_buffer[node_ptrs_num].score;
      if (d_score >= min_score) {
        node_last_match_ptr = start_symbol_ptr + node_ptr->last_match_index;
        score = (float)d_score;
        // find the position in the score list this node would go in
        U16 score_position, new_score_position, node_scores_search_size;
        new_score_position = num_node_scores;
        node_scores_search_size = num_node_scores + 1;
        do {
          node_scores_search_size = (node_scores_search_size + 1) >> 1;
          if (node_scores_search_size > new_score_position)
            node_scores_search_size = new_score_position;
          if (score > node_scores[node_scores_index[new_score_position - node_scores_search_size]].score)
            new_score_position -= node_scores_search_size;
        } while (node_scores_search_size > 1);

        next_child_ptr = string_nodes + node_ptr->child_node_num;
        num_symbols_in_string = rank_scores_buffer[node_ptrs_num].node_num_symbols;
        U32 new_score_lmi1, new_score_lmi2, new_score_smi1_m_1, new_score_smi2_m_1;
        // check for overlaps with better score list nodes
        new_score_lmi1 = next_child_ptr->last_match_index - 1;
        new_score_lmi2 = (U32)(node_last_match_ptr - start_symbol_ptr);

        if (new_score_lmi1 == new_score_lmi2) {
          U32 * sibling_node_num_ptr = &next_child_ptr->sibling_node_num[0];
          if (*sibling_node_num_ptr)
            new_score_lmi2 = string_nodes[*sibling_node_num_ptr].last_match_index - 1;
          else if (*(sibling_node_num_ptr + 1))
            new_score_lmi2 = string_nodes[*(sibling_node_num_ptr + 1)].last_match_index - 1;
          else if (*(sibling_node_num_ptr + 2))
            new_score_lmi2 = string_nodes[*(sibling_node_num_ptr + 2)].last_match_index - 1;
          else if (*(sibling_node_num_ptr + 3))
            new_score_lmi2 = string_nodes[*(sibling_node_num_ptr + 3)].last_match_index - 1;
          else {
            new_score_smi1_m_1 = new_score_lmi1 - num_symbols_in_string;
            score_position = 0;
            while (score_position < new_score_position) {
              U32 score_last_match_index1;
              score_index = node_scores_index[score_position];
              node_score_num_symbols = node_scores[score_index].num_symbols;
              score_last_match_index1 = node_scores[score_index].last_match_index1;
              if (new_score_lmi1 <= score_last_match_index1 - node_score_num_symbols)
                score_position++;
              else {
                U32 score_last_match_index2;
                score_last_match_index2 = node_scores[score_index].last_match_index2;
                if (score_last_match_index2 <= new_score_smi1_m_1)
                  score_position++;
                else if ((score_last_match_index1 <= new_score_smi1_m_1)
                    && (new_score_lmi1 <= score_last_match_index2 - node_score_num_symbols))
                  score_position++;
                else
                  goto rank_scores_thread_node_done;
              }
            }
            // no better overlapping score list nodes, so node will be put on the list
            // look for subsequent overlaps that should be removed (only looks for one to avoid min score reduction)
            if (score_position < num_node_scores) {
              U32 eslmi1, eslmi2;
              score_index = node_scores_index[score_position];
              eslmi1 = node_scores[score_index].last_match_index1;
              eslmi2 = node_scores[score_index].last_match_index2;
              node_score_num_symbols = node_scores[score_index].num_symbols;

rank_scores_thread_check_overlap_lmi_equal:
              if ((new_score_lmi1 > eslmi1 - node_score_num_symbols) && (eslmi2 > new_score_smi1_m_1)
                  && ((eslmi1 > new_score_smi1_m_1) || (new_score_lmi1 > eslmi2 - node_score_num_symbols)))
                goto rank_scores_thread_move_down;
              if (++score_position == num_node_scores)
                goto rank_scores_thread_check_max;
              score_index = node_scores_index[score_position];
              eslmi1 = node_scores[score_index].last_match_index1;
              eslmi2 = node_scores[score_index].last_match_index2;
              node_score_num_symbols = node_scores[score_index].num_symbols;
              goto rank_scores_thread_check_overlap_lmi_equal;
            }
          }
        }
        if (new_score_lmi2 < new_score_lmi1) {
          U32 temp_lmi = new_score_lmi1;
          new_score_lmi1 = new_score_lmi2;
          new_score_lmi2 = temp_lmi;
        }
        new_score_smi2_m_1 = new_score_lmi2 - num_symbols_in_string;
        new_score_smi1_m_1 = new_score_lmi1 - num_symbols_in_string;
        score_position = 0;
        while (score_position < new_score_position) {
          U32 score_last_match_index1;
          score_index = node_scores_index[score_position];
          node_score_num_symbols = node_scores[score_index].num_symbols;
          score_last_match_index1 = node_scores[score_index].last_match_index1;
          if (new_score_lmi2 <= score_last_match_index1 - node_score_num_symbols)
            score_position++;
          else {
            U32 score_last_match_index2;
            score_last_match_index2 = node_scores[score_index].last_match_index2;
            if (score_last_match_index2 <= new_score_smi1_m_1)
              score_position++;
            else if (score_last_match_index1 <= new_score_smi2_m_1) {
              if (new_score_lmi1 <= score_last_match_index1 - node_score_num_symbols) {
                if ((new_score_lmi2 <= score_last_match_index2 - node_score_num_symbols)
                    || (score_last_match_index2 <= new_score_smi2_m_1))
                  score_position++;
                else
                  goto rank_scores_thread_node_done;
              }
              else if (score_last_match_index1 <= new_score_smi1_m_1) {
                if (new_score_lmi2 <= score_last_match_index2 - node_score_num_symbols)
                  score_position++;
                else if (score_last_match_index2 <= new_score_smi2_m_1) {
                  if (new_score_lmi1 <= score_last_match_index2 - node_score_num_symbols)
                    score_position++;
                  else
                    goto rank_scores_thread_node_done;
                }
                else
                  goto rank_scores_thread_node_done;
              }
              else
                goto rank_scores_thread_node_done;
            }
            else
              goto rank_scores_thread_node_done;
          }
        }
        // no better overlapping score list nodes, so node will be put on the list
        // look for subsequent overlaps that should be removed (only looks for one to avoid min score reduction)
        if (score_position < num_node_scores) {
          U32 eslmi1, eslmi2;
          score_index = node_scores_index[score_position];
          eslmi1 = node_scores[score_index].last_match_index1;
          eslmi2 = node_scores[score_index].last_match_index2;
          node_score_num_symbols = node_scores[score_index].num_symbols;

rank_scores_thread_check_overlap_lmi_not_equal:
          if ((new_score_lmi2 > eslmi1 - node_score_num_symbols)
              && (eslmi2 > new_score_smi1_m_1)
              && ((new_score_lmi1 > eslmi1 - node_score_num_symbols)
                || (eslmi1 > new_score_smi2_m_1)
                || ((new_score_lmi2 > eslmi2 - node_score_num_symbols) && (eslmi2 > new_score_smi2_m_1)))
              && ((eslmi1 > new_score_smi1_m_1)
                || (new_score_lmi1 > eslmi2 - node_score_num_symbols)
                || ((new_score_lmi2 > eslmi2 - node_score_num_symbols) && (eslmi2 > new_score_smi2_m_1))))
            goto rank_scores_thread_move_down;
          if (++score_position == num_node_scores)
            goto rank_scores_thread_check_max;
          score_index = node_scores_index[score_position];
          eslmi1 = node_scores[score_index].last_match_index1;
          eslmi2 = node_scores[score_index].last_match_index2;
          node_score_num_symbols = node_scores[score_index].num_symbols;
          goto rank_scores_thread_check_overlap_lmi_not_equal;
        }

rank_scores_thread_check_max:
        if (num_node_scores != max_scores) { // increment the list length if not at limit
          node_scores_index[num_node_scores] = num_node_scores;
          num_node_scores++;
        }
        else // otherwise throw away the lowest score instead of moving it
          score_position--;

rank_scores_thread_move_down:
        // move the lower scoring nodes down one location
        score_index = node_scores_index[score_position];
        while (score_position > new_score_position) {
          node_scores_index[score_position] = node_scores_index[score_position - 1];
          score_position--;
        }
        // save the new score
        node_scores_index[score_position] = score_index;
        node_scores[score_index].score = score;
        node_scores[score_index].num_symbols = num_symbols_in_string;
        node_scores[score_index].last_match_index1 = new_score_lmi1;
        node_scores[score_index].last_match_index2 = new_score_lmi2;
        if (num_node_scores == max_scores)
          min_score = (double)node_scores[node_scores_index[max_scores-1]].score;
      }
rank_scores_thread_node_done:
      rank_scores_buffer[node_ptrs_num++].node_ptrs = 0;
    }
  } while ((size_t)node_ptr != 1);
  rank_scores_buffer[node_ptrs_num].node_ptrs = 0;
  return(0);
}



void *rank_scores_thread_UTF8_compliant(void *arg)
{
  struct string_node *node_ptr, *next_child_ptr;
  double d_score;
  float score;
  U32 *node_last_match_ptr;
  U16 num_symbols_in_string, score_index, node_score_num_symbols;
  U16 node_ptrs_num = 0;

  do {
    node_ptr = (struct string_node *)rank_scores_buffer[node_ptrs_num].node_ptrs;
    if ((size_t)node_ptr > 1) {
      d_score = rank_scores_buffer[node_ptrs_num].score;
      if (d_score >= min_score) {
        node_last_match_ptr = start_symbol_ptr + node_ptr->last_match_index;
        if ((node_ptr->symbol == (U32)' ') && (*(node_last_match_ptr-1) != (U32)' ')) {
          d_score *= 0.03;
          if (d_score < min_score)
            goto rank_scores_thread_UTF8_compliant_node_done;
        }
        else {
          if (node_ptr->symbol == 'C')
            d_score *= 1.5;
          if (*(node_last_match_ptr - rank_scores_buffer[node_ptrs_num].node_num_symbols) == (U32)'C')
            d_score *= 1.5;
        }
        score = (float)d_score;
        // find the position in the score list this node would go in
        U16 score_position, new_score_position, node_scores_search_size;
        new_score_position = num_node_scores;
        node_scores_search_size = num_node_scores + 1;
        do {
          node_scores_search_size = (node_scores_search_size + 1) >> 1;
          if (node_scores_search_size > new_score_position)
            node_scores_search_size = new_score_position;
          if (score > node_scores[node_scores_index[new_score_position - node_scores_search_size]].score)
            new_score_position -= node_scores_search_size;
        } while (node_scores_search_size > 1);

        next_child_ptr = string_nodes + node_ptr->child_node_num;
        num_symbols_in_string = rank_scores_buffer[node_ptrs_num].node_num_symbols;
        U32 new_score_lmi1, new_score_lmi2, new_score_smi1_m_1, new_score_smi2_m_1;
        // check for overlaps with better score list nodes
        new_score_lmi1 = next_child_ptr->last_match_index - 1;
        new_score_lmi2 = (U32)(node_last_match_ptr - start_symbol_ptr);

        if (new_score_lmi1 == new_score_lmi2) {
          U32 * sibling_node_num_ptr = &next_child_ptr->sibling_node_num[0];
          if (*sibling_node_num_ptr)
            new_score_lmi2 = string_nodes[*sibling_node_num_ptr].last_match_index - 1;
          else if (*(sibling_node_num_ptr + 1))
            new_score_lmi2 = string_nodes[*(sibling_node_num_ptr + 1)].last_match_index - 1;
          else if (*(sibling_node_num_ptr + 2))
            new_score_lmi2 = string_nodes[*(sibling_node_num_ptr + 2)].last_match_index - 1;
          else if (*(sibling_node_num_ptr + 3))
            new_score_lmi2 = string_nodes[*(sibling_node_num_ptr + 3)].last_match_index - 1;
          else {
            new_score_smi1_m_1 = new_score_lmi1 - num_symbols_in_string;
            score_position = 0;
            while (score_position < new_score_position) {
              U32 score_last_match_index1;
              score_index = node_scores_index[score_position];
              node_score_num_symbols = node_scores[score_index].num_symbols;
              score_last_match_index1 = node_scores[score_index].last_match_index1;
              if (new_score_lmi1 <= score_last_match_index1 - node_score_num_symbols)
                score_position++;
              else {
                U32 score_last_match_index2;
                score_last_match_index2 = node_scores[score_index].last_match_index2;
                if (score_last_match_index2 <= new_score_smi1_m_1)
                  score_position++;
                else if ((score_last_match_index1 <= new_score_smi1_m_1)
                    && (new_score_lmi1 <= score_last_match_index2 - node_score_num_symbols))
                  score_position++;
                else
                  goto rank_scores_thread_UTF8_compliant_node_done;
              }
            }
            // no better overlapping score list nodes, so node will be put on the list
            // look for subsequent overlaps that should be removed (only looks for one to avoid min score reduction)
            if (score_position < num_node_scores) {
              U32 eslmi1, eslmi2;
              score_index = node_scores_index[score_position];
              eslmi1 = node_scores[score_index].last_match_index1;
              eslmi2 = node_scores[score_index].last_match_index2;
              node_score_num_symbols = node_scores[score_index].num_symbols;

rank_scores_thread_UTF8_compliant_check_overlap_lmi_equal:
              if ((new_score_lmi1 > eslmi1 - node_score_num_symbols) && (eslmi2 > new_score_smi1_m_1)
                  && ((eslmi1 > new_score_smi1_m_1) || (new_score_lmi1 > eslmi2 - node_score_num_symbols)))
                goto rank_scores_thread_UTF8_compliant_move_down;
              if (++score_position == num_node_scores)
                goto rank_scores_thread_UTF8_compliant_check_max;
              score_index = node_scores_index[score_position];
              eslmi1 = node_scores[score_index].last_match_index1;
              eslmi2 = node_scores[score_index].last_match_index2;
              node_score_num_symbols = node_scores[score_index].num_symbols;
              goto rank_scores_thread_UTF8_compliant_check_overlap_lmi_equal;
            }
          }
        }
        if (new_score_lmi2 < new_score_lmi1) {
          U32 temp_lmi = new_score_lmi1;
          new_score_lmi1 = new_score_lmi2;
          new_score_lmi2 = temp_lmi;
        }
        new_score_smi2_m_1 = new_score_lmi2 - num_symbols_in_string;
        new_score_smi1_m_1 = new_score_lmi1 - num_symbols_in_string;
        score_position = 0;
        while (score_position < new_score_position) {
          U32 score_last_match_index1;
          score_index = node_scores_index[score_position];
          node_score_num_symbols = node_scores[score_index].num_symbols;
          score_last_match_index1 = node_scores[score_index].last_match_index1;
          if (new_score_lmi2 <= score_last_match_index1 - node_score_num_symbols)
            score_position++;
          else {
            U32 score_last_match_index2;
            score_last_match_index2 = node_scores[score_index].last_match_index2;
            if (score_last_match_index2 <= new_score_smi1_m_1)
              score_position++;
            else if (score_last_match_index1 <= new_score_smi2_m_1) {
              if (new_score_lmi1 <= score_last_match_index1 - node_score_num_symbols) {
                if ((new_score_lmi2 <= score_last_match_index2 - node_score_num_symbols)
                    || (score_last_match_index2 <= new_score_smi2_m_1))
                  score_position++;
                else
                  goto rank_scores_thread_UTF8_compliant_node_done;
              }
              else if (score_last_match_index1 <= new_score_smi1_m_1) {
                if (new_score_lmi2 <= score_last_match_index2 - node_score_num_symbols)
                  score_position++;
                else if (score_last_match_index2 <= new_score_smi2_m_1) {
                  if (new_score_lmi1 <= score_last_match_index2 - node_score_num_symbols)
                    score_position++;
                  else
                    goto rank_scores_thread_UTF8_compliant_node_done;
                }
                else
                  goto rank_scores_thread_UTF8_compliant_node_done;
              }
              else
                goto rank_scores_thread_UTF8_compliant_node_done;
            }
            else
              goto rank_scores_thread_UTF8_compliant_node_done;
          }
        }
        // no better overlapping score list nodes, so node will be put on the list
        // look for subsequent overlaps that should be removed (only looks for one to avoid min score reduction)
        if (score_position < num_node_scores) {
          U32 eslmi1, eslmi2;
          score_index = node_scores_index[score_position];
          eslmi1 = node_scores[score_index].last_match_index1;
          eslmi2 = node_scores[score_index].last_match_index2;
          node_score_num_symbols = node_scores[score_index].num_symbols;

rank_scores_thread_UTF8_compliant_check_overlap_lmi_not_equal:
          if ((new_score_lmi2 > eslmi1 - node_score_num_symbols)
              && (eslmi2 > new_score_smi1_m_1)
              && ((new_score_lmi1 > eslmi1 - node_score_num_symbols)
                || (eslmi1 > new_score_smi2_m_1)
                || ((new_score_lmi2 > eslmi2 - node_score_num_symbols) && (eslmi2 > new_score_smi2_m_1)))
              && ((eslmi1 > new_score_smi1_m_1)
                || (new_score_lmi1 > eslmi2 - node_score_num_symbols)
                || ((new_score_lmi2 > eslmi2 - node_score_num_symbols) && (eslmi2 > new_score_smi2_m_1))))
            goto rank_scores_thread_UTF8_compliant_move_down;
          if (++score_position == num_node_scores)
            goto rank_scores_thread_UTF8_compliant_check_max;
          score_index = node_scores_index[score_position];
          eslmi1 = node_scores[score_index].last_match_index1;
          eslmi2 = node_scores[score_index].last_match_index2;
          node_score_num_symbols = node_scores[score_index].num_symbols;
          goto rank_scores_thread_UTF8_compliant_check_overlap_lmi_not_equal;
        }

rank_scores_thread_UTF8_compliant_check_max:
        if (num_node_scores != max_scores) { // increment the list length if not at limit
          node_scores_index[num_node_scores] = num_node_scores;
          num_node_scores++;
        }
        else // otherwise throw away the lowest score instead of moving it
          score_position--;

rank_scores_thread_UTF8_compliant_move_down:
        // move the lower scoring nodes down one location
        score_index = node_scores_index[score_position];
        while (score_position > new_score_position) {
          node_scores_index[score_position] = node_scores_index[score_position - 1];
          score_position--;
        }
        // save the new score
        node_scores_index[score_position] = score_index;
        node_scores[score_index].score = score;
        node_scores[score_index].num_symbols = num_symbols_in_string;
        node_scores[score_index].last_match_index1 = new_score_lmi1;
        node_scores[score_index].last_match_index2 = new_score_lmi2;
        if (num_node_scores == max_scores)
          min_score = (double)node_scores[node_scores_index[max_scores-1]].score;
      }
rank_scores_thread_UTF8_compliant_node_done:
      rank_scores_buffer[node_ptrs_num++].node_ptrs = 0;
    }
  } while ((size_t)node_ptr != 1);
  rank_scores_buffer[node_ptrs_num].node_ptrs = 0;
  return(0);
}



void score_node(struct string_node* node_ptr, double string_entropy)
{
  struct string_node *next_child_ptr;
  U16 num_symbols_in_string, level;
  num_symbols_in_string = 2;
  level = 0;

  while (1) {
top_score_loop:
    node_instances = node_ptr->instances;
    if (node_instances >= 2)  {
      node_data[level].string_entropy = string_entropy;
      string_entropy += symbol_entropy[node_ptr->symbol];
      next_child_ptr = &string_nodes[node_ptr->child_node_num];

      if ((node_instances != next_child_ptr->instances) || (*(start_symbol_ptr + node_ptr->last_match_index + 1) == 0x20)) {
        // calculate this child's score
        double repeats = (double)(node_instances - 1);
        double profit_per_substitution;
        if (node_instances < NUM_PRECALCULATED_MATCH_RATIO_LOGS)
          profit_per_substitution = string_entropy - new_symbol_cost[node_instances];
        else
          profit_per_substitution = string_entropy - (log2_num_symbols_plus_substitution_cost - log2(repeats));
        if (profit_per_substitution >= 0.0) {
          double total_bit_savings_minus_production_cost = repeats * profit_per_substitution - production_cost;
          if (total_bit_savings_minus_production_cost > 0.0) {
            double profit_ratio = profit_per_substitution / string_entropy;
            double score = total_bit_savings_minus_production_cost * pow(profit_ratio, profit_ratio_power);
            if (score >= min_score) {
              if ((node_ptrs_num & 0xFFF) == 0)
                while (rank_scores_buffer[(U16)(node_ptrs_num + 0x1000)].node_ptrs != 0);
              rank_scores_buffer[node_ptrs_num].score = score;
              rank_scores_buffer[node_ptrs_num].node_num_symbols = num_symbols_in_string;
              rank_scores_buffer[node_ptrs_num++].node_ptrs = (size_t)node_ptr;
            }
          }
        }
      }
      node_data[level].node_ptr = node_ptr;
      node_data[level].num_symbols_in_string = num_symbols_in_string++;
      node_data[level++].next_sibling = 0;
      node_ptr = next_child_ptr;
      goto top_score_loop;
    }

    U32 sib_node_num = node_ptr->sibling_node_num[0];
    if (sib_node_num == 0) {
      sib_node_num = node_ptr->sibling_node_num[1];
      if (sib_node_num == 0) {
        sib_node_num = node_ptr->sibling_node_num[2];
        if (sib_node_num == 0) {
          sib_node_num = node_ptr->sibling_node_num[3];
          if (sib_node_num == 0) {
            while (level--) {
              U8 sibling_number = node_data[level].next_sibling;
              node_ptr = node_data[level].node_ptr;
              if (sibling_number != 3) {
                if (sibling_number != 2) {
                  if (sibling_number == 0) {
                    if (node_ptr->sibling_node_num[0]) {
                      node_ptr = &string_nodes[node_ptr->sibling_node_num[0]];
                      num_symbols_in_string = node_data[level].num_symbols_in_string;
                      string_entropy = node_data[level].string_entropy;
                      node_data[level++].next_sibling = 1;
                      goto top_score_loop;
                    }
                  }
                  if (node_ptr->sibling_node_num[1]) {
                    node_ptr = &string_nodes[node_ptr->sibling_node_num[1]];
                    num_symbols_in_string = node_data[level].num_symbols_in_string;
                    string_entropy = node_data[level].string_entropy;
                    node_data[level++].next_sibling = 2;
                    goto top_score_loop;
                  }
                }
                if (node_ptr->sibling_node_num[2]) {
                  node_ptr = &string_nodes[node_ptr->sibling_node_num[2]];
                  num_symbols_in_string = node_data[level].num_symbols_in_string;
                  string_entropy = node_data[level].string_entropy;
                  node_data[level++].next_sibling = 3;
                  goto top_score_loop;
                }
              }
              if (node_ptr->sibling_node_num[3]) {
                node_ptr = &string_nodes[node_ptr->sibling_node_num[3]];
                num_symbols_in_string = node_data[level].num_symbols_in_string;
                string_entropy = node_data[level].string_entropy;
                goto top_score_loop;
              }
            }
            return;
          }
          else
            node_ptr = &string_nodes[sib_node_num];
        }
        else {
          node_data[level].node_ptr = node_ptr;
          node_data[level].num_symbols_in_string = num_symbols_in_string;
          node_data[level].string_entropy = string_entropy;
          node_data[level++].next_sibling = 3;
          node_ptr = &string_nodes[sib_node_num];
        }
      }
      else {
        node_data[level].node_ptr = node_ptr;
        node_data[level].num_symbols_in_string = num_symbols_in_string;
        node_data[level].string_entropy = string_entropy;
        node_data[level++].next_sibling = 2;
        node_ptr = &string_nodes[sib_node_num];
      }
    }
    else {
      node_data[level].node_ptr = node_ptr;
      node_data[level].num_symbols_in_string = num_symbols_in_string;
      node_data[level].string_entropy = string_entropy;
      node_data[level++].next_sibling = 1;
      node_ptr = &string_nodes[sib_node_num];
    }
  }
}



void *build_lcp_thread(void *arg)
{
  struct lcp_thread_data *thread_data_ptr;
  U32 min_symbol, max_symbol, next_string_node_num, string_node_num_limit;
  U32 *in_symbol_ptr, *recent_stop_symbol_ptr;

  thread_data_ptr = (struct lcp_thread_data *)arg;
  in_symbol_ptr = (U32 *)min_symbol_ptr;
  min_symbol = thread_data_ptr->min_symbol;
  max_symbol = thread_data_ptr->max_symbol;
  next_string_node_num = thread_data_ptr->first_string_node_num;
  string_node_num_limit = thread_data_ptr->string_nodes_limit - MAX_STRING_LENGTH;

  while ((U32 * volatile)max_symbol_ptr != in_symbol_ptr) {
    recent_stop_symbol_ptr = (U32 *)stop_symbol_ptr;
    while (in_symbol_ptr != recent_stop_symbol_ptr) {
      if (next_string_node_num < string_node_num_limit) {
        U32 this_symbol;
        this_symbol = *in_symbol_ptr++;
        if ((this_symbol >= min_symbol) && (this_symbol <= max_symbol))
          add_suffix(this_symbol,in_symbol_ptr,&next_string_node_num);
      }
      else
        in_symbol_ptr = recent_stop_symbol_ptr;
    }
    thread_data_ptr->current_symbol_ptr = in_symbol_ptr;
  }
  return(0);
}



#define score_nodes(max_symbol) \
{ \
  while (i1 <= max_symbol) { \
    if (*base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],symbol_entropy[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],symbol_entropy[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],symbol_entropy[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],symbol_entropy[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],symbol_entropy[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],symbol_entropy[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],symbol_entropy[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],symbol_entropy[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],symbol_entropy[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],symbol_entropy[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],symbol_entropy[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],symbol_entropy[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],symbol_entropy[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],symbol_entropy[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],symbol_entropy[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],symbol_entropy[i1]); \
    ++base_node_child_num_ptr; \
    i1++; \
  } \
  while (rank_scores_buffer[node_ptrs_num].node_ptrs != 0); \
}



void *overlap_check_thread(void *arg)
{
  struct overlap_check_data *thread_data_ptr;
  struct match_node *match_node_ptr;
  U32 this_symbol, prior_match_score_number[MAX_PRIOR_MATCHES];
  U32 *prior_match_end_ptr[MAX_PRIOR_MATCHES];
  U32 *in_symbol_ptr;
  U32 *end_symbol_ptr;
  U32 num_prior_matches = 0;

  thread_data_ptr = (struct overlap_check_data *)arg;
  in_symbol_ptr = thread_data_ptr->start_symbol_ptr;
  end_symbol_ptr = thread_data_ptr->stop_symbol_ptr;

thread_overlap_check_loop_no_match:
  if (in_symbol_ptr == end_symbol_ptr)
    return(0);
  this_symbol = *in_symbol_ptr++;
  if ((int)this_symbol < 0)
    goto thread_overlap_check_loop_no_match;
  if (match_nodes[this_symbol].num_symbols == 0)
    goto thread_overlap_check_loop_no_match;
  match_node_ptr = &match_nodes[this_symbol];

thread_overlap_check_loop_match:
  if (in_symbol_ptr == end_symbol_ptr)
    return(0);
  this_symbol = *in_symbol_ptr++;
  if ((int)this_symbol < 0)
    goto thread_overlap_check_loop_no_match;
  match_node_ptr = match_node_ptr->child_ptr;
  if (this_symbol != match_node_ptr->symbol) {
    U32 shifted_symbol = this_symbol;
    do {
      if (match_node_ptr->sibling_node_num[shifted_symbol & 0xF] != 0) {
        match_node_ptr = &match_nodes[match_node_ptr->sibling_node_num[shifted_symbol & 0xF]];
        shifted_symbol = shifted_symbol >> 4;
      }
      else {
        if (match_node_ptr->miss_ptr == 0) {
          if (match_nodes[this_symbol].num_symbols == 0)
            goto thread_overlap_check_loop_no_match;
          match_node_ptr = &match_nodes[this_symbol];
          goto thread_overlap_check_loop_match;
        }
        else {
          match_node_ptr = match_node_ptr->miss_ptr;
          shifted_symbol = this_symbol;
        }
      }
    } while (this_symbol != match_node_ptr->symbol);
  }
  if (match_node_ptr->child_ptr)
    goto thread_overlap_check_loop_match;

  // no child, so found a match - check for overlaps
  U32 i1;
  U8 found_same_score_prior_match = 0;
  U32 node_score_number = match_node_ptr->score_number;
  U32 prior_match_number = 0;
  while (prior_match_number < num_prior_matches) {
    if (in_symbol_ptr - match_node_ptr->num_symbols > prior_match_end_ptr[prior_match_number]) {
      num_prior_matches--;
      for (i1 = prior_match_number ; i1 < num_prior_matches ; i1++) {
        prior_match_end_ptr[i1] = prior_match_end_ptr[i1+1];
        prior_match_score_number[i1] = prior_match_score_number[i1+1];
      }
    }
    else { // overlapping symbol substitution strings, so invalidate the lower score
      if (prior_match_score_number[prior_match_number] > node_score_number)
        node_scores_bad[prior_match_score_number[prior_match_number]] = 1;
      else if (prior_match_score_number[prior_match_number] != node_score_number)
        node_scores_bad[node_score_number] = 1;
      else
        found_same_score_prior_match = 1;
      prior_match_number++;
    }
  }
  match_node_ptr = match_node_ptr->hit_ptr;
  if (found_same_score_prior_match == 0) {
    prior_match_end_ptr[num_prior_matches] = in_symbol_ptr - 1;
    prior_match_score_number[num_prior_matches++] = node_score_number;
  }
  if (match_node_ptr == 0)
    goto thread_overlap_check_loop_no_match;
  else
    goto thread_overlap_check_loop_match;
  return(0);
}



void *substitute_thread(void *arg)
{
  U32 * end_data_ptr;
  U32 * near_end_data_ptr;
  U32 data = 0;
  U16 substitute_data_index = 0;
  U32 * old_data_ptr = start_symbol_ptr;

  while (data != 0xFFFFFFFF) {
    if (data) {
      if ((int)data > 0) {
substitute_copy:
        end_data_ptr = out_symbol_ptr + data;
        near_end_data_ptr = end_data_ptr - 32;
        while (out_symbol_ptr < near_end_data_ptr) {
          *(U64 *)out_symbol_ptr = *(U64 *)old_data_ptr;
          *((U64 *)out_symbol_ptr + 1) = *((U64 *)old_data_ptr + 1);
          *((U64 *)out_symbol_ptr + 2) = *((U64 *)old_data_ptr + 2);
          *((U64 *)out_symbol_ptr + 3) = *((U64 *)old_data_ptr + 3);
          *((U64 *)out_symbol_ptr + 4) = *((U64 *)old_data_ptr + 4);
          *((U64 *)out_symbol_ptr + 5) = *((U64 *)old_data_ptr + 5);
          *((U64 *)out_symbol_ptr + 6) = *((U64 *)old_data_ptr + 6);
          *((U64 *)out_symbol_ptr + 7) = *((U64 *)old_data_ptr + 7);
          *((U64 *)out_symbol_ptr + 8) = *((U64 *)old_data_ptr + 8);
          *((U64 *)out_symbol_ptr + 9) = *((U64 *)old_data_ptr + 9);
          *((U64 *)out_symbol_ptr + 10) = *((U64 *)old_data_ptr + 10);
          *((U64 *)out_symbol_ptr + 11) = *((U64 *)old_data_ptr + 11);
          *((U64 *)out_symbol_ptr + 12) = *((U64 *)old_data_ptr + 12);
          *((U64 *)out_symbol_ptr + 13) = *((U64 *)old_data_ptr + 13);
          *((U64 *)out_symbol_ptr + 14) = *((U64 *)old_data_ptr + 14);
          *((U64 *)out_symbol_ptr + 15) = *((U64 *)old_data_ptr + 15);
          old_data_ptr += 32;
          out_symbol_ptr += 32;
        }
        while (out_symbol_ptr < end_data_ptr - 1) {
          *(U64 *)out_symbol_ptr = *(U64 *)old_data_ptr;
          old_data_ptr += 2;
          out_symbol_ptr += 2;
        }
        while (out_symbol_ptr != end_data_ptr)
          *out_symbol_ptr++ = *old_data_ptr++;
        substitute_data[substitute_data_index++] = 0;
        data = substitute_data[substitute_data_index];
        if ((int)data < (int)0xFFFFFFFF)
          goto substitute_new_symbol;
      }
      else {
substitute_new_symbol:
        substitute_data[substitute_data_index++] = 0;
        old_data_ptr += (size_t)(data - 0x80000000);
        while (substitute_data[substitute_data_index] == 0);
        U32 symbol = substitute_data[substitute_data_index];
        symbol_count[symbol]++;
        *out_symbol_ptr++ = symbol;
        substitute_data[substitute_data_index++] = 0;
        data = substitute_data[substitute_data_index];
        if ((int)data > 0)
          goto substitute_copy;
      }
    }
    else
      data = substitute_data[substitute_data_index];
  }
  substitute_data[substitute_data_index] = 0;
  return(0);
}




void *find_substitutions_thread(void *arg)
{
  struct match_node *match_node_ptr;
  U32 this_symbol, node_score_number;
  struct find_substitutions_data * thread_data_ptr = (struct find_substitutions_data *)arg;
  U32 * in_symbol_ptr = (U32 *)thread_data_ptr->start_symbol_ptr;
  U32 * end_symbol_ptr = thread_data_ptr->stop_symbol_ptr;
  U32 substitute_index = 0;
  U32 num_symbols_to_copy = 0;

  thread_data_ptr->extra_match_symbols = 0;
  if (in_symbol_ptr == end_symbol_ptr)
    goto thread_symbol_substitution_loop_end;
  this_symbol = *in_symbol_ptr++;
  if ((int)this_symbol >= 0) {
thread_symbol_substitution_loop_no_match_with_symbol:
    match_node_ptr = &match_nodes[this_symbol];
    if (match_node_ptr->num_symbols) {
      this_symbol = *in_symbol_ptr++;
      if ((int)this_symbol >= 0) {
        if (match_node_ptr->child_ptr == 0) {
          if (num_symbols_to_copy >= 100000) {
            if (substitute_index == 0x400000) {
              thread_data_ptr->num_substitutions += 0x400000;
              substitute_index = 0;
              while (thread_data_ptr->data[0x3FFFFF]);
            }
            thread_data_ptr->data[substitute_index++] = num_symbols_to_copy;
            num_symbols_to_copy = 0;
          }
          if (in_symbol_ptr == end_symbol_ptr)
            goto thread_symbol_substitution_loop_end;
          this_symbol = *in_symbol_ptr++;
          if ((int)this_symbol >= 0)
            goto thread_symbol_substitution_loop_no_match_with_symbol;
          num_symbols_to_copy++;
          if (in_symbol_ptr == end_symbol_ptr)
            goto thread_symbol_substitution_loop_end;
          this_symbol = *in_symbol_ptr++;
          goto thread_symbol_substitution_loop_no_match_with_symbol;
        }
thread_symbol_substitution_loop_match_with_child:
        match_node_ptr = match_node_ptr->child_ptr;
        if (this_symbol != match_node_ptr->symbol) {
          U32 sibling_nibble = this_symbol;
          do {
            if (match_node_ptr->sibling_node_num[sibling_nibble & 0xF]) {
              match_node_ptr = &match_nodes[match_node_ptr->sibling_node_num[sibling_nibble & 0xF]];
              sibling_nibble = sibling_nibble >> 4;
            }
            else { // no match, so use miss node and output missed symbols
              if (match_node_ptr->miss_ptr == 0) {
                if (match_nodes[this_symbol].num_symbols) {
                  if (in_symbol_ptr > end_symbol_ptr) {
                    num_symbols_to_copy += match_node_ptr->num_symbols - (in_symbol_ptr - end_symbol_ptr);
                    goto thread_symbol_substitution_loop_end;
                  }
                  sibling_nibble = sibling_nibble >> 4;
                  num_symbols_to_copy += match_node_ptr->num_symbols - 1;
                  match_node_ptr = &match_nodes[this_symbol];
                }
                else {
                  if (in_symbol_ptr >= end_symbol_ptr) {
                    num_symbols_to_copy += match_node_ptr->num_symbols - (in_symbol_ptr - end_symbol_ptr);
                    goto thread_symbol_substitution_loop_end;
                  }
                  num_symbols_to_copy += match_node_ptr->num_symbols;
                  if (num_symbols_to_copy >= 100000) {
                    if (substitute_index == 0x400000) {
                      thread_data_ptr->num_substitutions += 0x400000;
                      substitute_index = 0;
                      while (thread_data_ptr->data[0x3FFFFF]);
                    }
                    thread_data_ptr->data[substitute_index++] = num_symbols_to_copy;
                    num_symbols_to_copy = 0;
                  }
                  if (in_symbol_ptr == end_symbol_ptr)
                    goto thread_symbol_substitution_loop_end;
                  this_symbol = *in_symbol_ptr++;
                  if ((int)this_symbol >= 0)
                    goto thread_symbol_substitution_loop_no_match_with_symbol;
                  num_symbols_to_copy++;
                  if (in_symbol_ptr == end_symbol_ptr)
                    goto thread_symbol_substitution_loop_end;
                  this_symbol = *in_symbol_ptr++;
                  goto thread_symbol_substitution_loop_no_match_with_symbol;
                }
              }
              else {
                num_symbols_to_copy += match_node_ptr->num_symbols - match_node_ptr->miss_ptr->num_symbols;
                if (in_symbol_ptr - match_node_ptr->miss_ptr->num_symbols >= end_symbol_ptr) {
                  num_symbols_to_copy -= in_symbol_ptr - end_symbol_ptr - match_node_ptr->miss_ptr->num_symbols;
                  goto thread_symbol_substitution_loop_end;
                }
                match_node_ptr = match_node_ptr->miss_ptr;
                sibling_nibble = this_symbol;
              }
            }
          } while (this_symbol != match_node_ptr->symbol);
        }
        if (match_node_ptr->child_ptr == 0) { // no child, so found a match
          if (num_symbols_to_copy) {
            if (substitute_index == 0x400000) {
              thread_data_ptr->num_substitutions += 0x400000;
              substitute_index = 0;
              while (thread_data_ptr->data[0x3FFFFF]);
            }
            thread_data_ptr->data[substitute_index++] = num_symbols_to_copy;
            num_symbols_to_copy = 0;
          }
          node_score_number = match_node_ptr->score_number;
          if (substitute_index == 0x400000) {
            thread_data_ptr->num_substitutions += 0x400000;
            substitute_index = 0;
            while (thread_data_ptr->data[0x3FFFFF]);
          }
          thread_data_ptr->data[substitute_index++] = 0x80000000 + match_node_ptr->num_symbols;
          if (substitute_index == 0x400000) {
            thread_data_ptr->num_substitutions += 0x400000;
            substitute_index = 0;
            while (thread_data_ptr->data[0x3FFFFF]);
          }
          thread_data_ptr->data[substitute_index++] = num_simple_symbols + new_symbol_number[node_score_number];
          if (in_symbol_ptr >= end_symbol_ptr) {
            thread_data_ptr->extra_match_symbols = in_symbol_ptr - end_symbol_ptr;
            goto thread_symbol_substitution_loop_end;
          }
          this_symbol = *in_symbol_ptr++;
          if ((int)this_symbol >= 0)
            goto thread_symbol_substitution_loop_no_match_with_symbol;
          num_symbols_to_copy++;
          if (in_symbol_ptr == end_symbol_ptr)
            goto thread_symbol_substitution_loop_end;
          this_symbol = *in_symbol_ptr++;
          goto thread_symbol_substitution_loop_no_match_with_symbol;
        }
        if (num_symbols_to_copy >= 100000) {
          if (substitute_index == 0x400000) {
            thread_data_ptr->num_substitutions += 0x400000;
            substitute_index = 0;
            while (thread_data_ptr->data[0x3FFFFF]);
          }
          thread_data_ptr->data[substitute_index++] = num_symbols_to_copy;
          num_symbols_to_copy = 0;
        }
        this_symbol = *in_symbol_ptr++;
        if ((int)this_symbol >= 0)
          goto thread_symbol_substitution_loop_match_with_child;
        num_symbols_to_copy += match_node_ptr->num_symbols + 1;
        if (in_symbol_ptr >= end_symbol_ptr) {
          num_symbols_to_copy -= in_symbol_ptr - end_symbol_ptr;
          goto thread_symbol_substitution_loop_end;
        }
        this_symbol = *in_symbol_ptr++;
        goto thread_symbol_substitution_loop_no_match_with_symbol;
      }
      else { // define symbol
        num_symbols_to_copy += match_node_ptr->num_symbols + 1;
        if (in_symbol_ptr >= end_symbol_ptr) {
          num_symbols_to_copy -= in_symbol_ptr - end_symbol_ptr;
          goto thread_symbol_substitution_loop_end;
        }
        this_symbol = *in_symbol_ptr++;
        goto thread_symbol_substitution_loop_no_match_with_symbol;
      }
    }
    if (++num_symbols_to_copy <= 100000) {
      if (in_symbol_ptr == end_symbol_ptr)
        goto thread_symbol_substitution_loop_end;
      this_symbol = *in_symbol_ptr++;
      if ((int)this_symbol >= 0)
        goto thread_symbol_substitution_loop_no_match_with_symbol;
      num_symbols_to_copy++;
      if (in_symbol_ptr == end_symbol_ptr)
        goto thread_symbol_substitution_loop_end;
      this_symbol = *in_symbol_ptr++;
      goto thread_symbol_substitution_loop_no_match_with_symbol;
    }
    if (substitute_index == 0x400000) {
      thread_data_ptr->num_substitutions += 0x400000;
      substitute_index = 0;
      while (thread_data_ptr->data[0x3FFFFF]);
    }
    thread_data_ptr->data[substitute_index++] = num_symbols_to_copy;
    num_symbols_to_copy = 0;
    if (in_symbol_ptr == end_symbol_ptr)
      goto thread_symbol_substitution_loop_end;
    this_symbol = *in_symbol_ptr++;
    if ((int)this_symbol >= 0)
      goto thread_symbol_substitution_loop_no_match_with_symbol;
    num_symbols_to_copy = 1;
    if (in_symbol_ptr == end_symbol_ptr)
      goto thread_symbol_substitution_loop_end;
    this_symbol = *in_symbol_ptr++;
    goto thread_symbol_substitution_loop_no_match_with_symbol;
  }
  else { // define symbol
    num_symbols_to_copy++;
    if (in_symbol_ptr == end_symbol_ptr)
      goto thread_symbol_substitution_loop_end;
    this_symbol = *in_symbol_ptr++;
    goto thread_symbol_substitution_loop_no_match_with_symbol;
  }

thread_symbol_substitution_loop_end:
  if (num_symbols_to_copy) {
    if (substitute_index == 0x400000) {
      thread_data_ptr->num_substitutions += 0x400000;
      substitute_index = 0;
      while (thread_data_ptr->data[0x3FFFFF]);
    }
    thread_data_ptr->data[substitute_index++] = num_symbols_to_copy;
  }
  thread_data_ptr->num_substitutions += substitute_index;
  thread_data_ptr->done = 1;
  return(0);
}



int main(int argc, char* argv[])
{
  FILE *fd_in, *fd_out;
  U64 available_RAM, *base_node_ptr;
  U32 in_size, num_file_symbols, num_start_symbols, num_compound_symbols, arg_num, i2;
  U32 UTF8_value, max_UTF8_value, symbol, num_symbols_to_copy;
  U32 first_symbol_number, node_score_number, suffix_node_number, next_string_node_num, string_node_num_limit;
  U32 *search_match_ptr, *match_strings, *match_string_start_ptr, *node_string_start_ptr, *base_node_child_num_ptr;
  U16 scan_cycle = 0;
  U8 UTF8_compliant, cap_encoded, user_set_RAM_size, this_char, delta_gap;
  U8 *free_RAM_ptr, *write_ptr;
  double d_file_symbols, prior_min_score, new_min_score, order_0_entropy, log_file_symbols, RAM_usage;
  float prior_cycle_start_ratio, prior_cycle_end_ratio;

  pthread_t build_lcp_thread1, build_lcp_thread2, build_lcp_thread3, build_lcp_thread4, build_lcp_thread5, build_lcp_thread6;
  pthread_t rank_scores_thread1, substitute_thread1;
  pthread_t overlap_check_threads[7];
  pthread_t find_substitutions_threads[7];


  clock_t start_time = clock();

  for (i1 = 0 ; i1 < MAX_SCORES ; i1++)
    node_scores_bad[i1] = 0;

  for (i1 = 0 ; i1 < 0x10000 ; i1++)
    substitute_data[i1] = 0;

  production_cost = 6.0;
  profit_ratio_power = 2.0;
  RAM_usage = 6.5;
  user_set_RAM_size = 0;
  arg_num = 1;
  while (*argv[arg_num] ==  '-') {
    if (*(argv[arg_num]+1) == 'm') {
      production_cost = (double)atof(argv[arg_num++]+2);
    }
    else if (*(argv[arg_num]+1) == 'p') {
      profit_ratio_power = (double)atof(argv[arg_num++]+2);
      if (profit_ratio_power < 0.0) {
        fprintf(stderr,"ERROR - p value must be >= 0.0\n");
        exit(0);
      }
    }
    else if (*(argv[arg_num]+1) == 'r') {
      user_set_RAM_size = 1;
      RAM_usage = (double)atof(argv[arg_num++]+2);
      if (RAM_usage < 5.0) {
        fprintf(stderr,"ERROR: -r value must be >= 5.0\n");
        exit(0);
      }
    }
    else {
      fprintf(stderr,"ERROR - Invalid '-' format.  Only -m<value>, -p<value> and -r<value> allowed\n");
      exit(0);
    }
  }

  if ((fd_in=fopen(argv[arg_num],"rb")) == NULL) {
    fprintf(stderr,"Error - unable to open input file '%s'\n",argv[arg_num]);
    exit(0);
  }
  arg_num++;
  fseek(fd_in, 0, SEEK_END);
  in_size = ftell(fd_in);
  rewind(fd_in);

  // Determine whether the RAM can be allocated, if not reduce size until malloc successful or RAM too small
  U64 max_memory_usage;
  if (sizeof(U32 *) >= 8)
    max_memory_usage = 0x800000000;
  else
    max_memory_usage = 0x70000000;
  if (user_set_RAM_size) {
    available_RAM = (U64)((double)in_size * RAM_usage) + 30000000;
    if (available_RAM > max_memory_usage)
      available_RAM = max_memory_usage;
  }
  else if (in_size > 260000000)
    if (13 * (U64)in_size / 2 < max_memory_usage)
      available_RAM = 13 * (U64)in_size / 2;
    else
      available_RAM = max_memory_usage;
  else
    available_RAM = 1690000000;

  start_symbol_ptr = (U32 *)malloc(available_RAM + 100000000 + 4 * in_size);
  if (start_symbol_ptr == 0) {
    fprintf(stderr,"ERROR - Insufficient RAM to compress - unable to allocate %Iu bytes for nodes\n",
        (size_t)(available_RAM + 100000000 + 4 * (U64)in_size));
    exit(0);
  }
  fprintf(stderr,"Allocated %Iu bytes for data processing\n",(size_t)available_RAM);

  char_buffer = (U8 *)start_symbol_ptr + 4 * (in_size + 1);
  in_symbol_ptr = start_symbol_ptr;

  i1 = fread(char_buffer,1,in_size,fd_in);
  fflush(fd_in);
  fclose(fd_in);
  fprintf(stderr,"Read %u byte input file\n",(unsigned int)i1);

  // parse the file to determine UTF8_compliant
  num_compound_symbols = 0;
  UTF8_compliant = 1;
  cap_encoded = *char_buffer & 1;
  delta_gap = *char_buffer >> 1;
  in_char_ptr = char_buffer + 1;
  end_char_ptr = char_buffer + in_size;

  if (in_char_ptr >= end_char_ptr) {
    num_node_scores = 0;
    goto write_file;
  }

  do {
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
        else
          in_char_ptr += 2;
      }
      else if (*in_char_ptr < 0xF0) {
        if ((*(in_char_ptr+1) < 0x80) || (*(in_char_ptr+1) >= 0xC0) || (*(in_char_ptr+2) >= 0xC0) || (*(in_char_ptr+2) >= 0xC0)) {
          UTF8_compliant = 0;
          break;
        }
        else
          in_char_ptr += 3;
      }
      else if (*in_char_ptr < 0xF2) {
        if ((*(in_char_ptr+1) < 0x80) || (*(in_char_ptr+1) >= 0xC0) || (*(in_char_ptr+2) < 0x80) || (*(in_char_ptr+2) >= 0xC0)
            || (*(in_char_ptr+3) < 0x80) || (*(in_char_ptr+3) >= 0xC0)) {
          UTF8_compliant = 0;
          break;
        }
        else
          in_char_ptr += 4;
      }
      else {
        UTF8_compliant = 0;
        break;
      }
    }
    else
      in_char_ptr++;
  } while (in_char_ptr < end_char_ptr);
  if (in_char_ptr > end_char_ptr)
    UTF8_compliant = 0;

  fprintf(stderr,"cap encoded: %u, UTF8 compliant %u\n",(unsigned int)cap_encoded,(unsigned int)UTF8_compliant);

  // parse the file to determine num_compound_symbols and max_UTF8_value
  num_file_symbols = 0;
  in_char_ptr = char_buffer + 1;

  if (UTF8_compliant) {
    num_simple_symbols = START_MY_SYMBOLS;
    first_symbol_number = 0x80000000 + START_MY_SYMBOLS;
    max_UTF8_value = 0;
    while (in_char_ptr != end_char_ptr) {
      this_char = *in_char_ptr++;
      if (this_char < 0x80)
        *in_symbol_ptr++ = (U32)this_char;
      else if (this_char == INSERT_SYMBOL_CHAR) {
        *in_symbol_ptr++ = START_MY_SYMBOLS + 0x10000 * (U32)*in_char_ptr + 0x100 * (U32)*(in_char_ptr+1) + (U32)*(in_char_ptr+2);
        in_char_ptr += 3;
      }
      else if (this_char == DEFINE_SYMBOL_CHAR) {
        *in_symbol_ptr++ = first_symbol_number + 0x10000 * (U32)*in_char_ptr
            + 0x100 * (U32)*(in_char_ptr+1) + (U32)*(in_char_ptr+2);
        in_char_ptr += 3;
        num_compound_symbols++;
      }
      else if (this_char >= 0x80) {
        if (this_char >= 0xF0) {
          UTF8_value = 0x40000 * (U32)(this_char & 0x7) + 0x1000 * (U32)(*in_char_ptr++ & 0x3F);
          UTF8_value += 0x40 * (U32)(*in_char_ptr++ & 0x3F);
          UTF8_value += (U32)*in_char_ptr++ & 0x3F;
        }
        else if (this_char >= 0xE0) {
          UTF8_value = 0x1000 * (U32)(this_char & 0xF) + 0x40 * (U32)(*in_char_ptr++ & 0x3F);
          UTF8_value += (U32)*in_char_ptr++ & 0x3F;
        }
        else 
          UTF8_value = 0x40 * (U32)(this_char & 0x1F) + (*in_char_ptr++ & 0x3F);
        if (UTF8_value > max_UTF8_value)
          max_UTF8_value = UTF8_value;
        *in_symbol_ptr++ = UTF8_value;
      }
      num_file_symbols++;
    }
    fprintf(stderr,"Found %u symbols, %u defines, maximum unicode value 0x%x\n",
        (unsigned int)num_file_symbols,(unsigned int)num_compound_symbols,(unsigned int)max_UTF8_value);
  }
  else {
    available_RAM += 4 * (U64)in_size;
    num_simple_symbols = 0x100;
    first_symbol_number = 0x80000000 + 0x100;
    while (in_char_ptr != end_char_ptr) {
      this_char = *in_char_ptr++;
      if (this_char < INSERT_SYMBOL_CHAR)
        *in_symbol_ptr++ = (U32)this_char;
      else {
        if (*in_char_ptr == DEFINE_SYMBOL_CHAR) {
          *in_symbol_ptr++ = (U32)this_char;
          in_char_ptr++;
        }
        else {
          if (this_char == INSERT_SYMBOL_CHAR)
            *in_symbol_ptr++ = 0x100 + 0x10000 * (U32)*in_char_ptr + 0x100 * (U32)*(in_char_ptr+1) + (U32)*(in_char_ptr+2);
          else {
            *in_symbol_ptr++ = first_symbol_number + 0x10000 * (U32)*in_char_ptr
                + 0x100 * (U32)*(in_char_ptr+1) + (U32)*(in_char_ptr+2);
            num_compound_symbols++;
          }
          in_char_ptr += 3;
        }
      }
      num_file_symbols++;
    }
    fprintf(stderr,"Found %u symbols, %u defines\n",(unsigned int)num_file_symbols,(unsigned int)num_compound_symbols);
  }
  end_symbol_ptr = in_symbol_ptr;
  *end_symbol_ptr = 0xFFFFFFFE;
  free_RAM_ptr = (U8 *)(end_symbol_ptr + 1);
  available_RAM = (available_RAM / 20) * 19;

  num_start_symbols = num_simple_symbols + num_compound_symbols;
  U64 *symbol_count_ptr;
  symbol_count_ptr = (U64 *)symbol_count;
  while (symbol_count_ptr < (U64 *)(symbol_count + num_start_symbols))
    *symbol_count_ptr++ = 0;

  // parse the data to determine symbol_counts
  in_symbol_ptr = start_symbol_ptr;
  do {
    symbol = *in_symbol_ptr++;
    while ((int)symbol >= 0) {
      symbol_count[symbol]++;
      symbol = *in_symbol_ptr++;
    }
  } while (symbol != 0xFFFFFFFE);

  log2_instances[1] = 0.0;
  for (i1=2 ; i1<NUM_PRECALCULATED_INSTANCE_LOGS ; i1++)
    log2_instances[i1] = log2((double)i1);

  i1 = 0x10000;
  while (i1--)
    rank_scores_buffer[i1].node_ptrs = 0;

  max_scores = 5000;
  min_score = production_cost;
  prior_min_score = min_score;
  prior_cycle_start_ratio = 0.0;
  prior_cycle_end_ratio = 1.0;

  do {
    num_start_symbols = num_simple_symbols + num_compound_symbols;
    num_file_symbols = end_symbol_ptr - start_symbol_ptr;
    *end_symbol_ptr = 0xFFFFFFFE;

    // Allocate memory for the log symbol count arrays
    if ((size_t)free_RAM_ptr % sizeof(double) != 0)
      free_RAM_ptr = (U8 *)(((size_t)free_RAM_ptr/sizeof(double) + 1) * sizeof(double));
    symbol_entropy = (double *)free_RAM_ptr;
    free_RAM_ptr += sizeof(double) * (size_t)num_start_symbols;

    // Set the memory addresses for the base_string_nodes_child_ptr array
    base_string_nodes_child_node_num = (U32 *)free_RAM_ptr;

    // pre-calculate log match ratios
    d_file_symbols = (double)num_file_symbols;
    log2_num_symbols_plus_substitution_cost = log2(d_file_symbols) + 1.4;
    for (i1 = 2 ; i1 < NUM_PRECALCULATED_MATCH_RATIO_LOGS ; i1++)
      // offset by 1 because the first instance is not a repeat
      new_symbol_cost[i1] = log2_num_symbols_plus_substitution_cost - log2((double)(i1-1));

    order_0_entropy = 0.0;
    log_file_symbols = log2(d_file_symbols);
    i1 = 0;

    do {
      if (symbol_count[i1] != 0) {
        if (symbol_count[i1] < NUM_PRECALCULATED_INSTANCE_LOGS) {
          double this_symbol_entropy = log_file_symbols - log2_instances[symbol_count[i1]];
          symbol_entropy[i1] = this_symbol_entropy;
          order_0_entropy += (double)symbol_count[i1] * this_symbol_entropy;
        }
        else {
          double d_symbol_count = (double)symbol_count[i1];
          double this_symbol_entropy = log_file_symbols - log2(d_symbol_count);
          symbol_entropy[i1] = this_symbol_entropy;
          order_0_entropy += d_symbol_count * this_symbol_entropy;
        }
      }
    } while (++i1 < num_simple_symbols);

    if (num_compound_symbols != 0) {
      while (i1 < num_start_symbols) {
        if (symbol_count[i1] < NUM_PRECALCULATED_INSTANCE_LOGS) {
          double this_symbol_entropy = log_file_symbols - log2_instances[symbol_count[i1]];
          symbol_entropy[i1] = this_symbol_entropy;
          order_0_entropy += (double)symbol_count[i1++] * this_symbol_entropy;
        }
        else {
          double d_symbol_count = (double)symbol_count[i1];
          double this_symbol_entropy = log_file_symbols - log2(d_symbol_count);
          symbol_entropy[i1++] = this_symbol_entropy;
          order_0_entropy += d_symbol_count * this_symbol_entropy;
        }
      }
      double d_symbol_count = (double)num_compound_symbols;
      double this_symbol_entropy = log_file_symbols - log2(d_symbol_count);
      order_0_entropy += d_symbol_count * this_symbol_entropy;
    }
    fprintf(stderr,"%u: %u syms, dict. size %u, %.4f bits/sym, o0e %u bytes\n",
        (unsigned int)++scan_cycle,(unsigned int)num_file_symbols,(unsigned int)num_compound_symbols,
        (float)(order_0_entropy/d_file_symbols),(unsigned int)(order_0_entropy*0.125));

    // setup to build the suffix tree
    base_node_ptr = (U64 *)base_string_nodes_child_node_num;
    while (base_node_ptr < (U64 *)(base_string_nodes_child_node_num
        + (num_start_symbols * BASE_NODES_CHILD_ARRAY_SIZE))) {
      *base_node_ptr = 0;
      *(base_node_ptr + 1) = 0;
      *(base_node_ptr + 2) = 0;
      *(base_node_ptr + 3) = 0;
      *(base_node_ptr + 4) = 0;
      *(base_node_ptr + 5) = 0;
      *(base_node_ptr + 6) = 0;
      *(base_node_ptr + 7) = 0;
      *(base_node_ptr + 8) = 0;
      *(base_node_ptr + 9) = 0;
      *(base_node_ptr + 10) = 0;
      *(base_node_ptr + 11) = 0;
      *(base_node_ptr + 12) = 0;
      *(base_node_ptr + 13) = 0;
      *(base_node_ptr + 14) = 0;
      *(base_node_ptr + 15) = 0;
      base_node_ptr += BASE_NODES_CHILD_ARRAY_SIZE;
    }
    num_node_scores = 0;

    // Set the memory adddress for the suffix tree nodes
    string_nodes = (struct string_node *)((size_t)free_RAM_ptr
        + sizeof(U32) * (size_t)num_start_symbols * BASE_NODES_CHILD_ARRAY_SIZE);
    string_node_num_limit = (U32)(((U8 *)start_symbol_ptr - (U8 *)string_nodes + available_RAM)
        / sizeof(struct string_node)) - MAX_STRING_LENGTH;

    if (1.0 - prior_cycle_end_ratio < prior_cycle_end_ratio - prior_cycle_start_ratio) {
      if ((1.0 - prior_cycle_end_ratio) * 1.5 < prior_cycle_end_ratio - prior_cycle_start_ratio) {
        prior_cycle_start_ratio = 0.0;
        in_symbol_ptr = start_symbol_ptr;
      }
      else {
        prior_cycle_start_ratio = 1.0 - 0.95 * (prior_cycle_end_ratio - prior_cycle_start_ratio);
        in_symbol_ptr = start_symbol_ptr + (U32)(prior_cycle_start_ratio * (float)(end_symbol_ptr - start_symbol_ptr));
      }
    }
    else {
      prior_cycle_start_ratio = prior_cycle_end_ratio;
      in_symbol_ptr = start_symbol_ptr + (U32)(prior_cycle_start_ratio * (float)(end_symbol_ptr - start_symbol_ptr));
    }

    next_string_node_num = 0;
    fprintf(stderr,"Common prefix scan 0 - %x\r",(unsigned int)(num_start_symbols-1));

    U32 sum_symbols, symbols_limit; 
    U32 main_max_symbol;
    U32 main_string_nodes_limit;
    i1 = 1;
    sum_symbols = symbol_count[0];
    symbols_limit = ((num_file_symbols - num_compound_symbols) / 100) * 7;
    while (sum_symbols < symbols_limit)
      sum_symbols += symbol_count[i1++];
    main_max_symbol = i1 - 1;
    lcp_thread_data[0].min_symbol = i1;
    symbols_limit = ((num_file_symbols - num_compound_symbols) / 100) * 15;
    while (sum_symbols < symbols_limit)
      sum_symbols += symbol_count[i1++];
    lcp_thread_data[0].max_symbol = i1 - 1;
    lcp_thread_data[1].min_symbol = i1;
    symbols_limit = ((num_file_symbols - num_compound_symbols) / 100) * 23;
    while (sum_symbols < symbols_limit)
      sum_symbols += symbol_count[i1++];
    lcp_thread_data[1].max_symbol = i1 - 1;
    lcp_thread_data[2].min_symbol = i1;
    symbols_limit = ((num_file_symbols - num_compound_symbols) / 100) * 32;
    while (sum_symbols < symbols_limit)
      sum_symbols += symbol_count[i1++];
    lcp_thread_data[2].max_symbol = i1 - 1;
    lcp_thread_data[3].min_symbol = i1;
    symbols_limit = ((num_file_symbols - num_compound_symbols) / 100) * 42;
    while (sum_symbols < symbols_limit)
      sum_symbols += symbol_count[i1++];
    lcp_thread_data[3].max_symbol = i1 - 1;
    lcp_thread_data[4].min_symbol = i1;
    symbols_limit = ((num_file_symbols - num_compound_symbols) / 100) * 53;
    while (sum_symbols < symbols_limit)
      sum_symbols += symbol_count[i1++];
    lcp_thread_data[4].max_symbol = i1 - 1;
    lcp_thread_data[5].min_symbol = i1;
    symbols_limit = ((num_file_symbols - num_compound_symbols) / 100) * 65;
    while (sum_symbols < symbols_limit)
      sum_symbols += symbol_count[i1++];
    lcp_thread_data[5].max_symbol = i1 - 1;
    lcp_thread_data[6].min_symbol = i1;
    symbols_limit = ((num_file_symbols - num_compound_symbols) / 100) * 69;
    while (sum_symbols < symbols_limit)
      sum_symbols += symbol_count[i1++];
    lcp_thread_data[6].max_symbol = i1 - 1;
    lcp_thread_data[7].min_symbol = i1;
    symbols_limit = ((num_file_symbols - num_compound_symbols) / 100) * 76;
    while (sum_symbols < symbols_limit)
      sum_symbols += symbol_count[i1++];
    lcp_thread_data[7].max_symbol = i1 - 1;
    lcp_thread_data[8].min_symbol = i1;
    symbols_limit = ((num_file_symbols - num_compound_symbols) / 100) * 83;
    while (sum_symbols < symbols_limit)
      sum_symbols += symbol_count[i1++];
    lcp_thread_data[8].max_symbol = i1 - 1;
    lcp_thread_data[9].min_symbol = i1;
    symbols_limit = ((num_file_symbols - num_compound_symbols) / 100) * 89;
    while (sum_symbols < symbols_limit)
      sum_symbols += symbol_count[i1++];
    lcp_thread_data[9].max_symbol = i1 - 1;
    lcp_thread_data[10].min_symbol = i1;
    symbols_limit = ((num_file_symbols - num_compound_symbols) / 100) * 95;
    while (sum_symbols < symbols_limit)
      sum_symbols += symbol_count[i1++];
    lcp_thread_data[10].max_symbol = i1 - 1;
    lcp_thread_data[11].min_symbol = i1;
    lcp_thread_data[11].max_symbol = num_start_symbols - 1;

    min_symbol_ptr = in_symbol_ptr;
    stop_symbol_ptr = in_symbol_ptr;
    max_symbol_ptr = 0;

    lcp_thread_data[6].first_string_node_num = 0;
    main_string_nodes_limit = (string_node_num_limit / 100) * 8 - MAX_STRING_LENGTH;
    lcp_thread_data[6].string_nodes_limit = (string_node_num_limit / 100) * 9;
    lcp_thread_data[0].first_string_node_num = (string_node_num_limit / 100) * 9;
    lcp_thread_data[7].first_string_node_num = (string_node_num_limit / 100) * 9;
    lcp_thread_data[0].string_nodes_limit = (string_node_num_limit / 100) * 22;
    lcp_thread_data[7].string_nodes_limit = (string_node_num_limit / 100) * 22;
    lcp_thread_data[1].first_string_node_num = (string_node_num_limit / 100) * 22;
    lcp_thread_data[8].first_string_node_num = (string_node_num_limit / 100) * 22;
    lcp_thread_data[1].string_nodes_limit = (string_node_num_limit / 100) * 35;
    lcp_thread_data[8].string_nodes_limit = (string_node_num_limit / 100) * 35;
    lcp_thread_data[2].first_string_node_num = (string_node_num_limit / 100) * 35;
    lcp_thread_data[9].first_string_node_num = (string_node_num_limit / 100) * 35;
    lcp_thread_data[2].string_nodes_limit = (string_node_num_limit / 100) * 49;
    lcp_thread_data[9].string_nodes_limit = (string_node_num_limit / 100) * 49;
    lcp_thread_data[3].first_string_node_num = (string_node_num_limit / 100) * 49;
    lcp_thread_data[10].first_string_node_num = (string_node_num_limit / 100) * 49;
    lcp_thread_data[3].string_nodes_limit = (string_node_num_limit / 100) * 65;
    lcp_thread_data[10].string_nodes_limit = (string_node_num_limit / 100) * 65;
    lcp_thread_data[4].first_string_node_num = (string_node_num_limit / 100) * 65;
    lcp_thread_data[11].first_string_node_num = (string_node_num_limit / 100) * 65;
    lcp_thread_data[4].string_nodes_limit = (string_node_num_limit / 100) * 82;
    lcp_thread_data[11].string_nodes_limit = (string_node_num_limit / 100) * 82;
    lcp_thread_data[5].first_string_node_num = (string_node_num_limit / 100) * 82;
    lcp_thread_data[5].string_nodes_limit = string_node_num_limit;

    pthread_create(&build_lcp_thread1,NULL,build_lcp_thread,(char *)&lcp_thread_data[0]);
    pthread_create(&build_lcp_thread2,NULL,build_lcp_thread,(char *)&lcp_thread_data[1]);
    pthread_create(&build_lcp_thread3,NULL,build_lcp_thread,(char *)&lcp_thread_data[2]);
    pthread_create(&build_lcp_thread4,NULL,build_lcp_thread,(char *)&lcp_thread_data[3]);
    pthread_create(&build_lcp_thread5,NULL,build_lcp_thread,(char *)&lcp_thread_data[4]);
    pthread_create(&build_lcp_thread6,NULL,build_lcp_thread,(char *)&lcp_thread_data[5]);

    while (next_string_node_num < main_string_nodes_limit) {
      this_symbol = *in_symbol_ptr++;
      while ((int)this_symbol >= 0) {
        if (this_symbol <= main_max_symbol) {
          add_suffix(this_symbol,in_symbol_ptr,&next_string_node_num);
          stop_symbol_ptr = in_symbol_ptr;
          if (next_string_node_num < main_string_nodes_limit)
            this_symbol = *in_symbol_ptr++;
          else
            goto done_building_lcp_tree;
        }
        else
          this_symbol = *in_symbol_ptr++;
      }
      if (this_symbol == 0xFFFFFFFE) {
        in_symbol_ptr--;
        break; // exit loop on EOF
      }
    }
done_building_lcp_tree:
    stop_symbol_ptr = in_symbol_ptr;
    max_symbol_ptr = in_symbol_ptr;

    base_node_child_num_ptr = base_string_nodes_child_node_num;
    node_ptrs_num = 0;
    if (UTF8_compliant)
      pthread_create(&rank_scores_thread1,NULL,rank_scores_thread_UTF8_compliant,(void *)&rank_scores_buffer[0]);
    else
      pthread_create(&rank_scores_thread1,NULL,rank_scores_thread,(void *)&rank_scores_buffer[0]);

    i1 = 0;
    score_nodes(main_max_symbol);
    while (rank_scores_buffer[(U16)(node_ptrs_num - 1)].node_ptrs != 0);

    pthread_join(build_lcp_thread1,NULL);
    pthread_create(&build_lcp_thread1,NULL,build_lcp_thread,(char *)&lcp_thread_data[6]);
    score_nodes(lcp_thread_data[0].max_symbol);
    while (rank_scores_buffer[(U16)(node_ptrs_num - 1)].node_ptrs != 0);

    pthread_join(build_lcp_thread2,NULL);
    pthread_create(&build_lcp_thread2,NULL,build_lcp_thread,(char *)&lcp_thread_data[7]);
    score_nodes(lcp_thread_data[1].max_symbol);
    while (rank_scores_buffer[(U16)(node_ptrs_num - 1)].node_ptrs != 0);

    pthread_join(build_lcp_thread3,NULL);
    pthread_create(&build_lcp_thread3,NULL,build_lcp_thread,(char *)&lcp_thread_data[8]);
    score_nodes(lcp_thread_data[2].max_symbol);
    while (rank_scores_buffer[(U16)(node_ptrs_num - 1)].node_ptrs != 0);

    pthread_join(build_lcp_thread4,NULL);
    pthread_create(&build_lcp_thread4,NULL,build_lcp_thread,(char *)&lcp_thread_data[9]);
    score_nodes(lcp_thread_data[3].max_symbol);
    while (rank_scores_buffer[(U16)(node_ptrs_num - 1)].node_ptrs != 0);

    pthread_join(build_lcp_thread5,NULL);
    pthread_create(&build_lcp_thread5,NULL,build_lcp_thread,(char *)&lcp_thread_data[10]);
    score_nodes(lcp_thread_data[4].max_symbol);
    while (rank_scores_buffer[(U16)(node_ptrs_num - 1)].node_ptrs != 0);

    pthread_join(build_lcp_thread6,NULL);
    pthread_create(&build_lcp_thread6,NULL,build_lcp_thread,(char *)&lcp_thread_data[11]);
    score_nodes(lcp_thread_data[5].max_symbol);

    pthread_join(build_lcp_thread1,NULL);
    score_nodes(lcp_thread_data[6].max_symbol);

    pthread_join(build_lcp_thread2,NULL);
    score_nodes(lcp_thread_data[7].max_symbol);

    pthread_join(build_lcp_thread3,NULL);
    score_nodes(lcp_thread_data[8].max_symbol);

    pthread_join(build_lcp_thread4,NULL);
    score_nodes(lcp_thread_data[9].max_symbol);

    pthread_join(build_lcp_thread5,NULL);
    score_nodes(lcp_thread_data[10].max_symbol);

    pthread_join(build_lcp_thread6,NULL);
    score_nodes(lcp_thread_data[11].max_symbol);
    while (rank_scores_buffer[(U16)(node_ptrs_num - 1)].node_ptrs != 0);

    rank_scores_buffer[node_ptrs_num].node_ptrs = 1;
    pthread_join(rank_scores_thread1,NULL);

    fprintf(stderr,"Read %u of %u symbols, start %.4f\n",
        (unsigned int)(in_symbol_ptr-start_symbol_ptr-(U32)(prior_cycle_start_ratio*(float)(end_symbol_ptr-start_symbol_ptr))),
        (unsigned int)(end_symbol_ptr-start_symbol_ptr),prior_cycle_start_ratio);
    prior_cycle_end_ratio = (float)(in_symbol_ptr-start_symbol_ptr)/(end_symbol_ptr-start_symbol_ptr);

    if (num_node_scores) {
      fprintf(stderr,"Common prefix scan 0 - %x, score[%hu] = %.3f\n",
          (unsigned int)(num_start_symbols-1),(unsigned short int)num_node_scores,
          node_scores[node_scores_index[num_node_scores-1]].score);

      free_RAM_ptr = (U8 *)(end_symbol_ptr + 1);
      match_nodes = (struct match_node *)free_RAM_ptr;
      match_nodes[0].num_symbols = 0;
      match_nodes[0].child_ptr = 0;

      // build a prefix tree of the match strings
      num_match_nodes = 1;
      i1 = 0;
      while (i1 < num_node_scores) {
        U32 *best_score_match_ptr;
        best_score_match_ptr = init_best_score_ptrs();
        match_node_ptr = match_nodes;
        while (best_score_match_ptr <= best_score_last_match_ptr) {
          this_symbol = *best_score_match_ptr;
          if (match_node_ptr->child_ptr == 0) {
            make_and_move_to_match_child();
          }
          else {
            U8 sibling_number;
            move_to_match_child(match_node_ptr,sibling_number);
            if (this_symbol == match_node_ptr->symbol) {
              if (match_node_ptr->child_ptr == 0) {
                node_scores_bad[i1] = 1;
                break;
              }
            }
            else
              make_and_move_to_match_sibling(0,i1,sibling_number);
          }
          best_score_match_ptr++;
        }
        if (match_node_ptr->child_ptr != 0)
          node_scores_bad[i1] = 1;
        i1++;
      }

      // span nodes entering the longest suffix matches and invalidating lower score if substring match found
      i1 = 0;
      while (i1 < num_node_scores) {
        U32 *best_score_match_ptr;
        best_score_match_ptr = init_best_score_ptrs();
        // read the first symbol
        this_symbol = *best_score_match_ptr++;
        match_node_ptr = &match_nodes[1];
        move_to_existing_match_sibling();
        while (best_score_match_ptr <= best_score_last_match_ptr) {
          // starting with the second symbol, look for suffixes that are in the prefix tree
          search_match_ptr = best_score_match_ptr;
          search_node_ptr = match_nodes;
          while (1) { // follow the tree until find child = 0 or sibling = 0
            if (search_node_ptr->child_ptr == 0) { // found a scored string that is a substring of this string
              if (search_node_ptr->score_number > i1)
                node_scores_bad[search_node_ptr->score_number] = 1;
              else if (search_node_ptr->score_number != i1)
                node_scores_bad[i1] = 1;
              break;
            }
            search_node_ptr = search_node_ptr->child_ptr;
            if (search_node_ptr == 0) // no children so exit suffix search
              break;
            this_symbol = *search_match_ptr;
            move_to_search_sibling();
            if (this_symbol != search_node_ptr->symbol) // no child match so exit suffix search
              break;
            match_node_ptr->miss_ptr = search_node_ptr;
            search_match_ptr++;
          }
          this_symbol = *best_score_match_ptr++;
        }
        i1++;
      }

      // Redo the tree build and miss values with just the valid score symbols
      match_node_ptr = match_nodes + num_start_symbols;
      while (match_node_ptr-- != match_nodes)
        match_node_ptr->num_symbols = 0;
      num_match_nodes = num_start_symbols;

      i1 = 0;
      while (i1 < num_node_scores) {
        if (node_scores_bad[i1] == 0) {
          U32 *best_score_match_ptr;
          best_score_match_ptr = init_best_score_ptrs();
          this_symbol = *best_score_match_ptr++;
          match_node_ptr = &match_nodes[this_symbol];
          best_score_num_symbols = 1;
          if (match_node_ptr->num_symbols == 0)
            init_level_1_match_node(this_symbol,i1);
          while (best_score_match_ptr <= best_score_last_match_ptr) {
            this_symbol = *best_score_match_ptr++;
            best_score_num_symbols++;
            move_to_match_child_with_make();
          }
        }
        i1++;
      }

      // span nodes entering the longest (first) suffix match for each node
      i1 = 0;
      while (i1 < num_node_scores) {
        if (node_scores_bad[i1] == 0) {
          U32 *best_score_suffix_ptr;
          best_score_suffix_ptr = init_best_score_ptrs();
          suffix_node_number = *best_score_suffix_ptr++;
          // starting at the node of the 2nd symbol in string, match strings with prefix tree until no match found,
          //   for each match node found, if suffix miss symbol is zero, set it to the tree symbol node
          while (best_score_suffix_ptr <= best_score_last_match_ptr) {
            // follow the suffix until the end (or break on no tree matches)
            this_symbol = *best_score_suffix_ptr++;
            suffix_node_number = match_nodes[suffix_node_number].child_ptr - match_nodes;
            U32 shifted_symbol = this_symbol;
            while (this_symbol != match_nodes[suffix_node_number].symbol) {
              suffix_node_number = match_nodes[suffix_node_number].sibling_node_num[shifted_symbol & 0xF];
              shifted_symbol = shifted_symbol >> 4;
            }
            match_node_ptr = &match_nodes[suffix_node_number];
            U32 *best_score_match_ptr;
            best_score_match_ptr = best_score_suffix_ptr;

            if (match_nodes[this_symbol].num_symbols != 0) {
              search_node_ptr = &match_nodes[this_symbol];
              if (match_node_ptr->child_ptr == 0) {
                if (match_node_ptr->hit_ptr == 0)
                  match_node_ptr->hit_ptr = search_node_ptr;
              }
              else
                write_all_children_miss_ptr();

              while (best_score_match_ptr <= best_score_last_match_ptr) {
                // follow the tree until end of match string or find child = 0 or sibling = 0
                if (search_node_ptr->child_ptr == 0) // no child, so done with this suffix
                  break;
                this_symbol = *best_score_match_ptr++;
                move_to_existing_match_child();
                move_to_search_child();
                if (this_symbol != search_node_ptr->symbol) // no matching sibling, so done with this suffix
                  break;
                if (match_node_ptr->child_ptr == 0) {
                  if (match_node_ptr->hit_ptr == 0)
                    match_node_ptr->hit_ptr = search_node_ptr;
                }
                else
                  write_all_children_miss_ptr();
              }
            }
          }
        }
        i1++;
      }

      // scan the data, following prefix tree
      fprintf(stderr,"Overlap search\r");

      U32 prior_match_score_number[MAX_PRIOR_MATCHES];
      U32 *prior_match_end_ptr[MAX_PRIOR_MATCHES]; 
      U32 num_prior_matches = 0;
      in_symbol_ptr = start_symbol_ptr;
      size_t block_size = (end_symbol_ptr - start_symbol_ptr) / 8;
      U32 * block_ptr = start_symbol_ptr + block_size;
      stop_symbol_ptr = block_ptr + MAX_STRING_LENGTH;

      if (stop_symbol_ptr > end_symbol_ptr)
        stop_symbol_ptr = end_symbol_ptr;
      overlap_check_data[0].start_symbol_ptr = block_ptr;
      block_ptr += block_size;
      overlap_check_data[0].stop_symbol_ptr = block_ptr + MAX_STRING_LENGTH;
      overlap_check_data[1].start_symbol_ptr = block_ptr;
      block_ptr += block_size;
      overlap_check_data[1].stop_symbol_ptr = block_ptr + MAX_STRING_LENGTH;
      overlap_check_data[2].start_symbol_ptr = block_ptr;
      block_ptr += block_size;
      overlap_check_data[2].stop_symbol_ptr = block_ptr + MAX_STRING_LENGTH;
      overlap_check_data[3].start_symbol_ptr = block_ptr;
      block_ptr += block_size;
      overlap_check_data[3].stop_symbol_ptr = block_ptr + MAX_STRING_LENGTH;
      overlap_check_data[4].start_symbol_ptr = block_ptr;
      block_ptr += block_size;
      overlap_check_data[4].stop_symbol_ptr = block_ptr + MAX_STRING_LENGTH;
      overlap_check_data[5].start_symbol_ptr = block_ptr;
      block_ptr += block_size;
      overlap_check_data[5].stop_symbol_ptr = block_ptr + MAX_STRING_LENGTH;
      overlap_check_data[6].start_symbol_ptr = block_ptr;
      overlap_check_data[6].stop_symbol_ptr = end_symbol_ptr;
      i1 = 5;
      while (overlap_check_data[i1].stop_symbol_ptr > end_symbol_ptr) {
        overlap_check_data[i1].stop_symbol_ptr = end_symbol_ptr;
        if (i1-- == 0)
          break;
      }

      for (i1 = 0 ; i1 < 7 ; i1++)
        pthread_create(&overlap_check_threads[i1],NULL,overlap_check_thread,(char *)&overlap_check_data[i1]);

      U8 found_same_score_prior_match;
      U32 prior_match_number;

main_overlap_check_loop_no_match:
      if (in_symbol_ptr == stop_symbol_ptr)
        goto main_overlap_check_loop_end;
      this_symbol = *in_symbol_ptr++;
      if ((int)this_symbol < 0)
        goto main_overlap_check_loop_no_match;
      if (match_nodes[this_symbol].num_symbols == 0)
        goto main_overlap_check_loop_no_match;
      match_node_ptr = &match_nodes[this_symbol];

main_overlap_check_loop_match:
      if (in_symbol_ptr == stop_symbol_ptr)
        goto main_overlap_check_loop_end;
      this_symbol = *in_symbol_ptr++;
      if ((int)this_symbol < 0)
        goto main_overlap_check_loop_no_match;

      match_node_ptr = match_node_ptr->child_ptr;
      if (this_symbol != match_node_ptr->symbol) {
        U32 shifted_symbol = this_symbol;
        do {
          if (match_node_ptr->sibling_node_num[shifted_symbol & 0xF] != 0) {
            match_node_ptr = &match_nodes[match_node_ptr->sibling_node_num[shifted_symbol & 0xF]];
            shifted_symbol = shifted_symbol >> 4;
          }
          else {
            if (match_node_ptr->miss_ptr == 0) {
              if (match_nodes[this_symbol].num_symbols == 0)
                goto main_overlap_check_loop_no_match;
              match_node_ptr = &match_nodes[this_symbol];
              goto main_overlap_check_loop_match;
            }
            else {
              match_node_ptr = match_node_ptr->miss_ptr;
              shifted_symbol = this_symbol;
            }
          }
        } while (this_symbol != match_node_ptr->symbol);
      }
      if (match_node_ptr->child_ptr)
        goto main_overlap_check_loop_match;

      // no child, so found a match - check for overlaps
      found_same_score_prior_match = 0;
      prior_match_number = 0;
      node_score_number = match_node_ptr->score_number;
      while (prior_match_number < num_prior_matches) {
        if (in_symbol_ptr - node_scores[node_scores_index[node_score_number]].num_symbols
            > prior_match_end_ptr[prior_match_number]) {
          num_prior_matches--;
          for (i2 = prior_match_number ; i2 < num_prior_matches ; i2++) {
            prior_match_end_ptr[i2] = prior_match_end_ptr[i2+1];
            prior_match_score_number[i2] = prior_match_score_number[i2+1];
          }
        }
        else { // overlapping symbol substitution strings, so invalidate the lower score
          if (prior_match_score_number[prior_match_number] > node_score_number)
            node_scores_bad[prior_match_score_number[prior_match_number]] = 1;
          else if (prior_match_score_number[prior_match_number] != node_score_number)
            node_scores_bad[node_score_number] = 1;
          else
            found_same_score_prior_match = 1;
          prior_match_number++;
        }
      }
      match_node_ptr = match_node_ptr->hit_ptr;
      if (found_same_score_prior_match == 0) {
        prior_match_end_ptr[num_prior_matches] = in_symbol_ptr - 1;
        prior_match_score_number[num_prior_matches++] = node_score_number;
      }
      if (match_node_ptr == 0)
        goto main_overlap_check_loop_no_match;
      else
        goto main_overlap_check_loop_match;

main_overlap_check_loop_end:
      for (i1 = 0 ; i1 < 7 ; i1++)
        pthread_join(overlap_check_threads[i1],NULL);

      // Redo the tree build and miss values with the final valid score symbols
      match_node_ptr = match_nodes + num_start_symbols;
      while (match_node_ptr-- != match_nodes)
        match_node_ptr->num_symbols = 0;

      num_match_nodes = num_start_symbols;
      max_string_length = 0;
      i2 = num_compound_symbols;
      i1 = 0;
      while (i1 < num_node_scores) {
        if (node_scores_bad[i1] == 0) {
          U32 *best_score_match_ptr;
          best_score_match_ptr = init_best_score_ptrs();
          this_symbol = *best_score_match_ptr++;
          best_score_num_symbols = 1;
          match_node_ptr = &match_nodes[this_symbol];
          if (match_node_ptr->num_symbols == 0)
            init_level_1_match_node(this_symbol,i1);
          while (best_score_match_ptr <= best_score_last_match_ptr) {
            this_symbol = *best_score_match_ptr++;
            best_score_num_symbols++;
            move_to_match_child_with_make();
          }
          if (best_score_num_symbols > max_string_length)
            max_string_length = best_score_num_symbols;
          symbol_count[num_simple_symbols+i2] = 0;
          new_symbol_number[i1] = i2++;
        }
        i1++;
      }
      max_string_length += 3;

      match_strings = (U32 *)((size_t)free_RAM_ptr + (size_t)num_match_nodes * sizeof(struct match_node));

      // span nodes entering the longest (first) suffix match for each node
      i1 = 0;
      while (i1 < num_node_scores) {
        if (node_scores_bad[i1] == 0) {
          U32 *best_score_suffix_ptr;
          best_score_suffix_ptr = init_best_score_ptrs();
          suffix_node_number = *best_score_suffix_ptr++;
          // starting at the node of the 2nd symbol in string, match strings with prefix tree until no match found,
          //   for each match node found, if suffix miss symbol is zero, set it to the tree symbol node
          while (best_score_suffix_ptr <= best_score_last_match_ptr) {
            // follow the suffix until the end (or break on no tree matches)
            this_symbol = *best_score_suffix_ptr++;
            suffix_node_number = match_nodes[suffix_node_number].child_ptr - match_nodes;
            U32 shifted_symbol = this_symbol;
            while (this_symbol != match_nodes[suffix_node_number].symbol) {
              suffix_node_number = match_nodes[suffix_node_number].sibling_node_num[shifted_symbol & 0xF];
              shifted_symbol = shifted_symbol >> 4;
            }
            match_node_ptr = &match_nodes[suffix_node_number];
            U32 *best_score_match_ptr;
            best_score_match_ptr = best_score_suffix_ptr;

            if (match_nodes[this_symbol].num_symbols != 0) {
              search_node_ptr = &match_nodes[this_symbol];
              if (match_node_ptr->child_ptr == 0) {
                if (match_node_ptr->hit_ptr == 0)
                  match_node_ptr->hit_ptr = search_node_ptr;
              }
              else
                write_all_children_miss_ptr();

              while (best_score_match_ptr <= best_score_last_match_ptr) {
                // follow the tree until end of match string or find child = 0 or sibling = 0
                if (search_node_ptr->child_ptr == 0) // no child, so done with this suffix
                  break;
                this_symbol = *best_score_match_ptr++;
                move_to_existing_match_child();
                move_to_search_child();
                if (this_symbol != search_node_ptr->symbol) // no matching sibling, so done with this suffix
                  break;
                if (match_node_ptr->child_ptr == 0) {
                  if (match_node_ptr->hit_ptr == 0)
                    match_node_ptr->hit_ptr = search_node_ptr;
                }
                else
                  write_all_children_miss_ptr();
              }
            }
          }
        }
        // save the match strings so they can be added to the end of the data after symbol substitution is done
        match_string_start_ptr = &match_strings[(U32)i1 * max_string_length];
        node_string_start_ptr = start_symbol_ptr + node_scores[node_scores_index[i1]].last_match_index1
          - node_scores[node_scores_index[i1]].num_symbols + 1;
        for (i2 = 0 ; i2 < node_scores[node_scores_index[i1]].num_symbols ; i2++)
          *(match_string_start_ptr + i2) = *(node_string_start_ptr + i2);
        i1++;
      }

      fprintf(stderr,"Replacing data with new dictionary symbols\r");
      // scan the data following the prefix tree and substitute new symbols on end matches (child is 0)
      if (end_symbol_ptr - start_symbol_ptr >= 1000000) {
        stop_symbol_ptr = start_symbol_ptr + ((end_symbol_ptr - start_symbol_ptr) >> 3);
        find_substitutions_data[0].start_symbol_ptr = stop_symbol_ptr;
        block_size = (end_symbol_ptr - start_symbol_ptr) / 7;
        block_ptr = stop_symbol_ptr + block_size;
        find_substitutions_data[0].stop_symbol_ptr = block_ptr;
        find_substitutions_data[1].start_symbol_ptr = block_ptr;
        block_ptr += block_size;
        find_substitutions_data[1].stop_symbol_ptr = block_ptr;
        find_substitutions_data[2].start_symbol_ptr = block_ptr;
        block_ptr += block_size;
        find_substitutions_data[2].stop_symbol_ptr = block_ptr;
        find_substitutions_data[3].start_symbol_ptr = block_ptr;
        block_ptr += block_size;
        find_substitutions_data[3].stop_symbol_ptr = block_ptr;
        find_substitutions_data[4].start_symbol_ptr = block_ptr;
        block_ptr += block_size;
        find_substitutions_data[4].stop_symbol_ptr = block_ptr;
        find_substitutions_data[5].start_symbol_ptr = block_ptr;
        find_substitutions_data[5].stop_symbol_ptr = end_symbol_ptr;
      }
      else {
        stop_symbol_ptr = end_symbol_ptr;
        find_substitutions_data[0].start_symbol_ptr = end_symbol_ptr;
        find_substitutions_data[0].stop_symbol_ptr = end_symbol_ptr;
        find_substitutions_data[1].start_symbol_ptr = end_symbol_ptr;
        find_substitutions_data[1].stop_symbol_ptr = end_symbol_ptr;
        find_substitutions_data[2].start_symbol_ptr = end_symbol_ptr;
        find_substitutions_data[2].stop_symbol_ptr = end_symbol_ptr;
        find_substitutions_data[3].start_symbol_ptr = end_symbol_ptr;
        find_substitutions_data[3].stop_symbol_ptr = end_symbol_ptr;
        find_substitutions_data[4].start_symbol_ptr = end_symbol_ptr;
        find_substitutions_data[4].stop_symbol_ptr = end_symbol_ptr;
        find_substitutions_data[5].start_symbol_ptr = end_symbol_ptr;
        find_substitutions_data[5].stop_symbol_ptr = end_symbol_ptr;
      }

      for (i1 = 0 ; i1 < 6 ; i1++) {
        find_substitutions_data[i1].done = 0;
        find_substitutions_data[i1].num_substitutions = 0;
        pthread_create(&find_substitutions_threads[i1],NULL,find_substitutions_thread,(char *)&find_substitutions_data[i1]);
      }

      U32 extra_match_symbols = 0;
      U16 substitute_index = 0;
      num_symbols_to_copy = 0;
      in_symbol_ptr = start_symbol_ptr;
      out_symbol_ptr = start_symbol_ptr;

      pthread_create(&substitute_thread1,NULL,substitute_thread,NULL);
      if (in_symbol_ptr == stop_symbol_ptr)
        goto main_symbol_substitution_loop_end;
      this_symbol = *in_symbol_ptr++;
      if ((int)this_symbol >= 0) {
main_symbol_substitution_loop_no_match_with_symbol:
        match_node_ptr = &match_nodes[this_symbol];
        if (match_node_ptr->num_symbols) {
          this_symbol = *in_symbol_ptr++;
          if ((int)this_symbol >= 0) {
            if (match_node_ptr->child_ptr == 0) {
              if (num_symbols_to_copy >= 100000) {
                if ((substitute_index & 0x7FFF) == 0x7FFF)
                  while (substitute_data[substitute_index & 0x8000]);
                substitute_data[substitute_index++] = num_symbols_to_copy;
                num_symbols_to_copy = 0;
              }
              if (in_symbol_ptr == stop_symbol_ptr)
                goto main_symbol_substitution_loop_end;
              this_symbol = *in_symbol_ptr++;
              if ((int)this_symbol >= 0)
                goto main_symbol_substitution_loop_no_match_with_symbol;
              num_symbols_to_copy++;
              if (in_symbol_ptr == stop_symbol_ptr)
                goto main_symbol_substitution_loop_end;
              this_symbol = *in_symbol_ptr++;
              goto main_symbol_substitution_loop_no_match_with_symbol;
            }
main_symbol_substitution_loop_match_with_child:
            match_node_ptr = match_node_ptr->child_ptr;
            if (this_symbol != match_node_ptr->symbol) {
              U32 sibling_nibble = this_symbol;
              do {
                if (match_node_ptr->sibling_node_num[sibling_nibble & 0xF]) {
                  match_node_ptr = &match_nodes[match_node_ptr->sibling_node_num[sibling_nibble & 0xF]];
                  sibling_nibble = sibling_nibble >> 4;
                }
                else { // no match, so use miss node and output missed symbols
                  if (match_node_ptr->miss_ptr == 0) {
                    if (match_nodes[this_symbol].num_symbols) {
                      if (in_symbol_ptr > stop_symbol_ptr) {
                        num_symbols_to_copy += match_node_ptr->num_symbols - (in_symbol_ptr - stop_symbol_ptr);
                        goto main_symbol_substitution_loop_end;
                      }
                      sibling_nibble = sibling_nibble >> 4;
                      num_symbols_to_copy += match_node_ptr->num_symbols - 1;
                      match_node_ptr = &match_nodes[this_symbol];
                    }
                    else {
                      if (in_symbol_ptr >= stop_symbol_ptr) {
                        num_symbols_to_copy += match_node_ptr->num_symbols - (in_symbol_ptr - stop_symbol_ptr);
                        goto main_symbol_substitution_loop_end;
                      }
                      num_symbols_to_copy += match_node_ptr->num_symbols;
                      if (num_symbols_to_copy >= 100000) {
                        if ((substitute_index & 0x7FFF) == 0x7FFF)
                          while (substitute_data[substitute_index & 0x8000]);
                        substitute_data[substitute_index++] = num_symbols_to_copy;
                        num_symbols_to_copy = 0;
                      }
                      if (in_symbol_ptr == stop_symbol_ptr)
                        goto main_symbol_substitution_loop_end;
                      this_symbol = *in_symbol_ptr++;
                      if ((int)this_symbol >= 0)
                        goto main_symbol_substitution_loop_no_match_with_symbol;
                      num_symbols_to_copy++;
                      if (in_symbol_ptr == stop_symbol_ptr)
                        goto main_symbol_substitution_loop_end;
                      this_symbol = *in_symbol_ptr++;
                      goto main_symbol_substitution_loop_no_match_with_symbol;
                    }
                  }
                  else {
                    num_symbols_to_copy += match_node_ptr->num_symbols - match_node_ptr->miss_ptr->num_symbols;
                    if (in_symbol_ptr - match_node_ptr->miss_ptr->num_symbols >= stop_symbol_ptr) {
                      num_symbols_to_copy -= in_symbol_ptr - stop_symbol_ptr - match_node_ptr->miss_ptr->num_symbols;
                      goto main_symbol_substitution_loop_end;
                    }
                    match_node_ptr = match_node_ptr->miss_ptr;
                    sibling_nibble = this_symbol;
                  }
                }
              } while (this_symbol != match_node_ptr->symbol);
            }
            if (match_node_ptr->child_ptr == 0) { // no child, so found a match
              if (num_symbols_to_copy) {
                if ((substitute_index & 0x7FFF) == 0x7FFF)
                  while (substitute_data[substitute_index & 0x8000]);
                substitute_data[substitute_index++] = num_symbols_to_copy;
                num_symbols_to_copy = 0;
              }
              node_score_number = match_node_ptr->score_number;
              if ((substitute_index & 0x7FFF) == 0x7FFF)
                while (substitute_data[substitute_index & 0x8000]);
              substitute_data[substitute_index++] = 0x80000000 + match_node_ptr->num_symbols;
              if ((substitute_index & 0x7FFF) == 0x7FFF)
                while (substitute_data[substitute_index & 0x8000]);
              substitute_data[substitute_index++] = num_simple_symbols + new_symbol_number[node_score_number];
              if (in_symbol_ptr >= stop_symbol_ptr) {
                extra_match_symbols = in_symbol_ptr - stop_symbol_ptr;
                goto main_symbol_substitution_loop_end;
              }
              this_symbol = *in_symbol_ptr++;
              if ((int)this_symbol >= 0)
                goto main_symbol_substitution_loop_no_match_with_symbol;
              num_symbols_to_copy++;
              if (in_symbol_ptr == stop_symbol_ptr)
                goto main_symbol_substitution_loop_end;
              this_symbol = *in_symbol_ptr++;
              goto main_symbol_substitution_loop_no_match_with_symbol;
            }
            if (num_symbols_to_copy >= 100000) {
              if ((substitute_index & 0x7FFF) == 0x7FFF)
                while (substitute_data[substitute_index & 0x8000]);
              substitute_data[substitute_index++] = num_symbols_to_copy;
              num_symbols_to_copy = 0;
            }
            this_symbol = *in_symbol_ptr++;
            if ((int)this_symbol >= 0)
              goto main_symbol_substitution_loop_match_with_child;
            num_symbols_to_copy += match_node_ptr->num_symbols + 1;
            if (in_symbol_ptr >= stop_symbol_ptr) {
              num_symbols_to_copy -= in_symbol_ptr - stop_symbol_ptr;
              goto main_symbol_substitution_loop_end;
            }
            this_symbol = *in_symbol_ptr++;
            goto main_symbol_substitution_loop_no_match_with_symbol;
          }
          else { // define symbol
            num_symbols_to_copy += match_node_ptr->num_symbols + 1;
            if (in_symbol_ptr >= stop_symbol_ptr) {
              num_symbols_to_copy -= in_symbol_ptr - stop_symbol_ptr;
              goto main_symbol_substitution_loop_end;
            }
            this_symbol = *in_symbol_ptr++;
            goto main_symbol_substitution_loop_no_match_with_symbol;
          }
        }
        if (++num_symbols_to_copy <= 100000) {
          if (in_symbol_ptr == stop_symbol_ptr)
            goto main_symbol_substitution_loop_end;
          this_symbol = *in_symbol_ptr++;
          if ((int)this_symbol >= 0)
            goto main_symbol_substitution_loop_no_match_with_symbol;
          num_symbols_to_copy++;
          if (in_symbol_ptr == stop_symbol_ptr)
            goto main_symbol_substitution_loop_end;
          this_symbol = *in_symbol_ptr++;
          goto main_symbol_substitution_loop_no_match_with_symbol;
        }
        if ((substitute_index & 0x7FFF) == 0x7FFF)
          while (substitute_data[substitute_index & 0x8000]);
        substitute_data[substitute_index++] = num_symbols_to_copy;
        num_symbols_to_copy = 0;
        if (in_symbol_ptr == stop_symbol_ptr)
          goto main_symbol_substitution_loop_end;
        this_symbol = *in_symbol_ptr++;
        if ((int)this_symbol >= 0)
          goto main_symbol_substitution_loop_no_match_with_symbol;
        num_symbols_to_copy = 1;
        if (in_symbol_ptr == stop_symbol_ptr)
          goto main_symbol_substitution_loop_end;
        this_symbol = *in_symbol_ptr++;
        goto main_symbol_substitution_loop_no_match_with_symbol;
      }
      else { // define symbol
        num_symbols_to_copy++;
        if (in_symbol_ptr == stop_symbol_ptr)
          goto main_symbol_substitution_loop_end;
        this_symbol = *in_symbol_ptr++;
        goto main_symbol_substitution_loop_no_match_with_symbol;
      }

main_symbol_substitution_loop_end:
      if (num_symbols_to_copy) {
        if ((substitute_index & 0x7FFF) == 0x7FFF)
          while (substitute_data[substitute_index & 0x8000]);
        substitute_data[substitute_index++] = num_symbols_to_copy;
      }

      for (i1 = 0 ; i1 < 6 ; i1++) {
        U32 num_substitutions;
        U32 i2 = 0;
top_sub:
        while (find_substitutions_data[i1].done == 0) {
          num_substitutions = find_substitutions_data[i1].num_substitutions;
          if (extra_match_symbols && num_substitutions) {
            if ((int)find_substitutions_data[i1].data[0] >= 0) {
              if (find_substitutions_data[i1].data[0] > extra_match_symbols) {
                find_substitutions_data[i1].data[0] -= extra_match_symbols;
                extra_match_symbols = 0;
              }
              else if (find_substitutions_data[i1].data[0] == extra_match_symbols) {
                i2 = 1;
                extra_match_symbols = 0;
              }
              else {
                find_substitutions_data[i1].done = 0;
                find_substitutions_data[i1].num_substitutions = 0;
                find_substitutions_data[i1].start_symbol_ptr += extra_match_symbols;
                pthread_create(&find_substitutions_threads[i1],NULL,find_substitutions_thread,
                    (char *)&find_substitutions_data[i1]);
                extra_match_symbols = 0;
                goto top_sub;
              }
            }
            else {
              find_substitutions_data[i1].done = 0;
              find_substitutions_data[i1].num_substitutions = 0;
              find_substitutions_data[i1].start_symbol_ptr += extra_match_symbols;
              pthread_create(&find_substitutions_threads[i1],NULL,find_substitutions_thread,(char *)&find_substitutions_data[i1]);
              extra_match_symbols = 0;
              goto top_sub;
            }
          }
          while (i2 != num_substitutions) { // send find_substitutions thread data
            if ((substitute_index & 0x7FFF) == 0x7FFF)
              while (substitute_data[substitute_index & 0x8000]);
            substitute_data[substitute_index++] = find_substitutions_data[i1].data[i2 & 0x3FFFFF];
            find_substitutions_data[i1].data[i2 & 0x3FFFFF] = 0;
            i2++;
          }
        }
        pthread_join(find_substitutions_threads[i1],NULL);
        num_substitutions = find_substitutions_data[i1].num_substitutions;
        if (extra_match_symbols) {
          if ((int)find_substitutions_data[i1].data[0] >= 0) {
            if (find_substitutions_data[i1].data[0] > extra_match_symbols) {
              find_substitutions_data[i1].data[0] -= extra_match_symbols;
              extra_match_symbols = 0;
            }
            else if (find_substitutions_data[i1].data[0] == extra_match_symbols) {
              i2 = 1;
              extra_match_symbols = 0;
            }
            else {
              find_substitutions_data[i1].done = 0;
              find_substitutions_data[i1].num_substitutions = 0;
              find_substitutions_data[i1].start_symbol_ptr += extra_match_symbols;
              pthread_create(&find_substitutions_threads[i1],NULL,find_substitutions_thread,(char *)&find_substitutions_data[i1]);
              extra_match_symbols = 0;
              goto top_sub;
            }
          }
          else {
            find_substitutions_data[i1].done = 0;
            find_substitutions_data[i1].num_substitutions = 0;
            find_substitutions_data[i1].start_symbol_ptr += extra_match_symbols;
            pthread_create(&find_substitutions_threads[i1],NULL,find_substitutions_thread,(char *)&find_substitutions_data[i1]);
            extra_match_symbols = 0;
            goto top_sub;
          }
        }
        while (i2 != num_substitutions) { // send find_substitutions thread data
          if ((substitute_index & 0x7FFF) == 0x7FFF)
            while (substitute_data[substitute_index & 0x8000]);
          substitute_data[substitute_index++] = find_substitutions_data[i1].data[i2 & 0x3FFFFF];
          find_substitutions_data[i1].data[i2 & 0x3FFFFF] = 0;
          i2++;
        }
        extra_match_symbols += find_substitutions_data[i1].extra_match_symbols;
      }

      if ((substitute_index & 0x7FFF) == 0x7FFF)
        while (substitute_data[substitute_index]);
      substitute_data[substitute_index] = 0xFFFFFFFF;
      pthread_join(substitute_thread1,NULL);

      // Add the new symbol definitions to the end of the data
      i1 = 0;
      while (i1 < num_node_scores) {
        if (node_scores_bad[i1] == 0) {
          U32 *match_string_ptr, *match_string_end_ptr;
          *out_symbol_ptr++ = first_symbol_number + num_compound_symbols++;
          match_string_ptr = match_strings + max_string_length * (U32)i1;
          match_string_end_ptr = match_string_ptr + node_scores[node_scores_index[i1++]].num_symbols;
          while (match_string_ptr != match_string_end_ptr) {
            symbol_count[*match_string_ptr] -= symbol_count[num_simple_symbols+num_compound_symbols-1] - 1;
            *out_symbol_ptr++ = *match_string_ptr++;
          }
        }
        else
          node_scores_bad[i1++] = 0;
      }
      end_symbol_ptr = out_symbol_ptr;
      *end_symbol_ptr = 0xFFFFFFFE;
      free_RAM_ptr = (U8 *)(end_symbol_ptr + 1);
    }

    if (num_node_scores) {
      if (scan_cycle > 1) {
        if (num_node_scores == max_scores) {
          if (min_score < prior_min_score) {
            if (scan_cycle > 50) {
              if (scan_cycle > 100)
                new_min_score = 0.993 * min_score * (min_score / prior_min_score);
              else
                new_min_score = 0.99 * min_score * (min_score / prior_min_score);
            }
            else
              new_min_score = 0.98 * min_score * (min_score / prior_min_score);
          }
          else
            new_min_score = 0.47 * (prior_min_score + min_score);
        }
        else {
          if (min_score < prior_min_score)
            new_min_score = 0.95 * min_score * (min_score / prior_min_score);
          else
            new_min_score = 0.45 * (prior_min_score + min_score);
        }
      }
      else {
        new_min_score = (double)(0.75 * min_score);
        prior_min_score = min_score;
      }
    }
    else if (min_score > 0.000000001) {
      new_min_score = 0.000000001;
      num_node_scores = 1;
    }
    if (min_score < prior_min_score)
      prior_min_score = min_score;
    if (new_min_score < prior_min_score)
      min_score = new_min_score;
    else
      min_score = 0.98 * prior_min_score;
    if (min_score < 0.000000001)
      min_score = 0.000000001;

    max_scores = (max_scores + 2 * (((29 * (num_simple_symbols + num_compound_symbols - num_start_symbols)) >> 5) + 5000)) / 3;
    if (max_scores > MAX_SCORES)
      max_scores = MAX_SCORES;
  } while (num_node_scores);

write_file:
  if ((fd_out = fopen(argv[arg_num],"wb+")) == NULL) {
    fprintf(stderr,"ERROR - unable to open output file '%s'\n",argv[arg_num]);
    exit(0);
  }
  if (in_size) {
    in_char_ptr = char_buffer;
    *in_char_ptr++ = cap_encoded + (delta_gap * 2);
    in_symbol_ptr = start_symbol_ptr;
    if (UTF8_compliant) {
      while (in_symbol_ptr != end_symbol_ptr) {
        U32 symbol_value;
        symbol_value = *in_symbol_ptr++;
        if (symbol_value < 0x80)
          *in_char_ptr++ = (U8)symbol_value;
        else if (symbol_value < 0x800) {
          *in_char_ptr++ = 0xC0 + (symbol_value >> 6);
          *in_char_ptr++ = 0x80 + (symbol_value & 0x3F);
        }
        else if (symbol_value < 0x10000) {
          *in_char_ptr++ = 0xE0 + (symbol_value >> 12);
          *in_char_ptr++ = 0x80 + ((symbol_value >> 6) & 0x3F);
          *in_char_ptr++ = 0x80 + (symbol_value & 0x3F);
        }
        else if (symbol_value < START_MY_SYMBOLS) {
          *in_char_ptr++ = 0xF0 + (symbol_value >> 18);
          *in_char_ptr++ = 0x80 + ((symbol_value >> 12) & 0x3F);
          *in_char_ptr++ = 0x80 + ((symbol_value >> 6) & 0x3F);
          *in_char_ptr++ = 0x80 + (symbol_value & 0x3F);
        }
        else if ((int)symbol_value >= 0) {
          symbol_value -= START_MY_SYMBOLS;
          *in_char_ptr++ = INSERT_SYMBOL_CHAR;
          *in_char_ptr++ = (U8)((symbol_value >> 16) & 0xFF);
          *in_char_ptr++ = (U8)((symbol_value >> 8) & 0xFF);
          *in_char_ptr++ = (U8)(symbol_value & 0xFF);
        }
        else {
          symbol_value -= 0x80000000 + START_MY_SYMBOLS;
          *in_char_ptr++ = DEFINE_SYMBOL_CHAR;
          *in_char_ptr++ = (U8)((symbol_value >> 16) & 0xFF);
          *in_char_ptr++ = (U8)((symbol_value >> 8) & 0xFF);
          *in_char_ptr++ = (U8)(symbol_value & 0xFF);
        }
      }
    }
    else {
      while (in_symbol_ptr != end_symbol_ptr) {
        U32 symbol_value;
        symbol_value = *in_symbol_ptr++;
        if (symbol_value < INSERT_SYMBOL_CHAR)
          *in_char_ptr++ = (U8)symbol_value;
        else if (symbol_value == INSERT_SYMBOL_CHAR) {
          *in_char_ptr++ = INSERT_SYMBOL_CHAR;
          *in_char_ptr++ = DEFINE_SYMBOL_CHAR;
        }
        else if (symbol_value == DEFINE_SYMBOL_CHAR) {
          *in_char_ptr++ = DEFINE_SYMBOL_CHAR;
          *in_char_ptr++ = DEFINE_SYMBOL_CHAR;
        }
        else if ((int)symbol_value >= 0) {
          symbol_value -= 0x100;
          *in_char_ptr++ = INSERT_SYMBOL_CHAR;
          *in_char_ptr++ = (U8)((symbol_value >> 16) & 0xFF);
          *in_char_ptr++ = (U8)((symbol_value >> 8) & 0xFF);
          *in_char_ptr++ = (U8)(symbol_value & 0xFF);
        }
        else {
          symbol_value -= 0x80000000 + 0x100;
          *in_char_ptr++ = DEFINE_SYMBOL_CHAR;
          *in_char_ptr++ = (U8)((symbol_value >> 16) & 0xFF);
          *in_char_ptr++ = (U8)((symbol_value >> 8) & 0xFF);
          *in_char_ptr++ = (U8)(symbol_value & 0xFF);
        }
      }
    }
    in_size = in_char_ptr - char_buffer;
    write_ptr = char_buffer;
    while (write_ptr + MAX_WRITE_SIZE < char_buffer + in_size) {
      fwrite(write_ptr,1,MAX_WRITE_SIZE,fd_out);
      write_ptr += MAX_WRITE_SIZE;
      fflush(fd_out);
    }
    fwrite(write_ptr,1,char_buffer+in_size-write_ptr,fd_out);
  }
  fclose(fd_out);
  free(start_symbol_ptr);
  fprintf(stderr,"Constructed %u rule grammar in %0.3f seconds.\n",
      num_compound_symbols,(float)(clock()-start_time)/CLOCKS_PER_SEC);
  return(0);
}


