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

// GLZAcompress.c
//   Iteratively does the following until there are not any tokens worth generating:
//     1. Counts the token occurances in the input data and calculates the log base 2 of each token's probability of occuring
//     2. Builds portions of the generalized suffix tree and searches them for the "most compressible" token strings
//     3. Invalidates less desireable strings that overlap with better ones
//     4. Replaces each occurance of the best strings with a new token and adds the best strings to the end of the file
//        with a unique (define) token marker at the start of the string
//
// Usage:
//   GLZAcompress [-m#] [-r#] <infilename> <outfilename>, where the first # is any non-negative number and sets the cutoff score
//       (default 4.5) and the second # is approximately the RAM usage / input file size ratio (default 6.5 for UTF-8 compliant
//       files, 10.5 for non UTF-8 compliant files, minimum is 5.0).

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <pthread.h>

const INSERT_TOKEN_CHAR = 0xFE;
const DEFINE_TOKEN_CHAR = 0xFF;
const START_MY_TOKENS = 0x00080000;
const size_t MAX_MEMORY_USAGE = 0x800000000;
const MAX_WRITE_SIZE = 0x200000;
const MAX_PRIOR_MATCHES = 20;
const MAX_STRING_LENGTH = 8000;
const BASE_NODES_CHILD_ARRAY_SIZE = 16;
const NUM_PRECALCULATED_INSTANCE_LOGS = 10000;
const NUM_PRECALCULATED_MATCH_RATIO_LOGS = 2000;
const MAX_SCORES = 30000;

static struct string_node {
  unsigned int token;
  unsigned int last_match_index;
  unsigned int sibling_node_num[4];
  unsigned int instances;
  unsigned int child_node_num;
} *string_nodes;

static struct match_node {
  unsigned int token;
  unsigned int num_tokens;
  unsigned int score_number;
  struct match_node *child_ptr;
  unsigned int sibling_node_num[16];
  struct match_node *miss_ptr;
  struct match_node *hit_ptr;
} *match_nodes, *match_node_ptr, *child_match_node_ptr, *search_node_ptr;

struct node_score_data {
  unsigned int last_match_index1;
  unsigned int last_match_index2;
  float score;
  unsigned short int num_tokens;
} node_scores[30000];

struct lcp_thread_data {
  unsigned int min_token;
  unsigned int max_token;
  unsigned int string_nodes_limit;
  unsigned int first_string_node_num;
  unsigned int *current_token_ptr;
} lcp_thread_data[12];

struct rank_scores_struct {
  double score;
  volatile size_t node_ptrs;
  short int node_num_tokens;
} rank_scores_buffer[0x10000];

struct score_data {
  struct string_node *node_ptr;
  double log_expected_match_ratio;
  unsigned short int num_tokens_in_string;
  unsigned char next_sibling;
} node_data[20000];

struct overlap_check_data {
  unsigned int *start_token_ptr;
  unsigned int *stop_token_ptr;
} overlap_check_data[7];

struct find_substitutions_data {
  volatile unsigned int *start_token_ptr;
  unsigned int *stop_token_ptr;
  volatile unsigned int data[0x400000];
  unsigned int extra_match_symbols;
  volatile unsigned int num_substitutions;
  volatile unsigned char done;
} find_substitutions_data[6];

unsigned int this_token, max_string_length, max_scores, i1;
unsigned int num_base_tokens, node_instances, num_match_nodes, best_score_num_tokens, sibling_node_number;
unsigned int new_token_number[30000];
unsigned int token_count[10000000];
unsigned int *start_token_ptr, *end_token_ptr, *in_token_ptr, *out_token_ptr, *min_token_ptr;
unsigned int *base_string_nodes_child_node_num, *best_score_last_match_ptr, *node_last_match_ptr;
unsigned int * volatile max_token_ptr;
unsigned int * volatile stop_token_ptr;
volatile unsigned int substitute_data[0x10000];
unsigned short int node_ptrs_num, num_node_scores, node_scores_index[30000];
double d_num_token_inv, min_score, cutoff_score;
double log_match_ratios[2000], log_instances[10000], d_num_tokens_in_string_inv[10000];
double *log_token_count_minus_log_num_tokens;
unsigned char node_scores_bad[30000];
unsigned char *char_buffer, *in_char_ptr, *out_char_ptr, *end_char_ptr;



static inline unsigned int* init_best_score_ptrs()
{
  best_score_last_match_ptr = node_scores[node_scores_index[i1]].last_match_index1 + start_token_ptr;
  return(best_score_last_match_ptr - node_scores[node_scores_index[i1]].num_tokens + 1);
}



#define init_match_node(match_num_tokens, match_score_number) \
{ \
  match_node_ptr->token = this_token; \
  match_node_ptr->num_tokens = match_num_tokens; \
  match_node_ptr->score_number = match_score_number; \
  match_node_ptr->child_ptr = 0; \
  size_t *sibling_nodes_ptr; \
  sibling_nodes_ptr = (size_t *)&match_node_ptr->sibling_node_num[0]; \
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



#define init_level_1_match_node(match_token, match_score_number) \
{ \
  match_node_ptr->token = match_token; \
  match_node_ptr->num_tokens = 1; \
  match_node_ptr->score_number = match_score_number; \
  match_node_ptr->child_ptr = 0; \
  size_t *sibling_nodes_ptr; \
  sibling_nodes_ptr = (size_t *)&match_node_ptr->sibling_node_num[0]; \
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
  unsigned int shifted_token = this_token; \
  sibling_number = (unsigned char)(shifted_token & 0xF); \
  while ((this_token != match_node_ptr->token) && (match_node_ptr->sibling_node_num[sibling_number] != 0)) { \
    match_node_ptr = &match_nodes[match_node_ptr->sibling_node_num[sibling_number]]; \
    shifted_token = shifted_token >> 4; \
    sibling_number = (unsigned char)(shifted_token & 0xF); \
  } \
}



#define move_to_match_child(match_node_ptr, sibling_number) \
{ \
  match_node_ptr = match_node_ptr->child_ptr; \
  move_to_match_sibling(match_node_ptr, sibling_number); \
}



#define move_to_existing_match_sibling() \
{ \
  unsigned int shifted_token = this_token; \
  unsigned char sibling_number = (unsigned char)(shifted_token & 0xF); \
  while (this_token != match_node_ptr->token) { \
    match_node_ptr = &match_nodes[match_node_ptr->sibling_node_num[sibling_number]]; \
    shifted_token = shifted_token >> 4; \
    sibling_number = (unsigned char)(shifted_token & 0xF); \
  } \
}



#define move_to_existing_match_child() \
{ \
  match_node_ptr = match_node_ptr->child_ptr; \
  move_to_existing_match_sibling(); \
}



static inline void move_to_search_sibling()
{
  unsigned char sibling_nibble, sibling_depth;
  unsigned int shifted_token;

  sibling_depth = 0;
  shifted_token = this_token;
  sibling_nibble = (unsigned char)(shifted_token & 0xF);
  while ((this_token != search_node_ptr->token) && (search_node_ptr->sibling_node_num[sibling_nibble] != 0)) {
    search_node_ptr = &match_nodes[search_node_ptr->sibling_node_num[sibling_nibble]];
    sibling_depth++;
    shifted_token = shifted_token >> 4;
    sibling_nibble = (unsigned char)(shifted_token & 0xF);
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
  init_match_node(best_score_num_tokens,i1); \
}



static inline void make_and_move_to_match_sibling(unsigned int num_tokens, unsigned int score_number,
    unsigned char sibling_number)
{
  match_node_ptr->sibling_node_num[sibling_number] = num_match_nodes;
  match_node_ptr = &match_nodes[num_match_nodes++];
  init_match_node(num_tokens,score_number);
  return;
}



static inline void move_to_match_child_with_make()
{
  if (match_node_ptr->child_ptr == 0) {
    make_and_move_to_match_child();
  }
  else {
    match_node_ptr = match_node_ptr->child_ptr;
    unsigned char sibling_number;
    move_to_match_sibling(match_node_ptr,sibling_number);
    if (this_token != match_node_ptr->token)
      make_and_move_to_match_sibling(best_score_num_tokens,i1,sibling_number);
  }
  return;
}



static inline void write_siblings_miss_ptr(struct match_node *child_ptr)
{
  unsigned char sibling_nibble;
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
  unsigned char sibling_nibble;
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



static inline void add_suffix(unsigned int this_token, unsigned int *in_token_ptr, unsigned int *next_string_node_num_ptr)
{
  unsigned int search_token, match_start_index;
  unsigned int *base_node_child_num_ptr, *node_data_ptr;
  struct string_node *child_ptr, *next_child_ptr;
  search_token = *in_token_ptr;
  base_node_child_num_ptr = &base_string_nodes_child_node_num[this_token * BASE_NODES_CHILD_ARRAY_SIZE + (search_token & 0xF)];
  if (*base_node_child_num_ptr) {
    unsigned int shifted_search_token;
    match_start_index = in_token_ptr - start_token_ptr - 1;
    child_ptr = &string_nodes[*base_node_child_num_ptr];
    if ((int)search_token >= 0) {
      shifted_search_token = search_token >> 4;
      while (search_token != child_ptr->token) { // follow siblings until match found or end of siblings found
        unsigned int *next_child_node_num_ptr;
        next_child_node_num_ptr = (unsigned int *)&child_ptr->sibling_node_num[shifted_search_token & 3];
        next_child_ptr = &string_nodes[*next_child_node_num_ptr];
        if (next_child_ptr != string_nodes) {
          child_ptr = next_child_ptr;
          shifted_search_token = shifted_search_token >> 2;
        }
        else { // no matching child so add sibling
          node_data_ptr = (unsigned int *)&string_nodes[*next_string_node_num_ptr];
          *node_data_ptr = *in_token_ptr;
          *(node_data_ptr+1) = (unsigned int)(in_token_ptr - start_token_ptr);
          *((unsigned long long *)node_data_ptr+1) = 0;
          *((unsigned long long *)node_data_ptr+2) = 0;
          *((unsigned long long *)node_data_ptr+3) = 1;
          *next_child_node_num_ptr = *next_string_node_num_ptr;
          *next_string_node_num_ptr += 1;
          return;
        }
      }
      // found a matching sibling
      if (child_ptr->child_node_num == 0) {
        // matching child without grandchild so create grandchild for previous instance then add string to grandchild
        node_data_ptr = (unsigned int *)&string_nodes[*next_string_node_num_ptr];
        *node_data_ptr = *(start_token_ptr + child_ptr->last_match_index + 1);
        *(node_data_ptr+1) = child_ptr->last_match_index + 1;
        *((unsigned long long *)node_data_ptr+1) = 0;
        *((unsigned long long *)node_data_ptr+2) = 0;
        *((unsigned long long *)node_data_ptr+3) = 1;
        child_ptr->child_node_num = *next_string_node_num_ptr;
        *next_string_node_num_ptr += 1;
      }
      if (match_start_index > child_ptr->last_match_index) {
        // increment instances and update last_match_index for strings that do not overlap
        child_ptr->instances++;
        child_ptr->last_match_index = (unsigned int)(in_token_ptr - start_token_ptr);
      }
      child_ptr = &string_nodes[child_ptr->child_node_num];

      unsigned int *next_child_node_num_ptr, *match_max_ptr;
      match_max_ptr = start_token_ptr + match_start_index + MAX_STRING_LENGTH;
      search_token = *++in_token_ptr;
      if (search_token != child_ptr->token) { // go to sibling and check for end of siblings
        if ((int)search_token < 0)
          return;
add_string_to_child_not_match:
        next_child_node_num_ptr = (unsigned int *)&child_ptr->sibling_node_num[search_token & 3];
        if (*next_child_node_num_ptr == 0)
          goto add_string_to_child_add_sibling;
        child_ptr = &string_nodes[*next_child_node_num_ptr];
        if (search_token != child_ptr->token) {
          shifted_search_token = search_token >> 2;
add_string_to_child_check_sibling:
          next_child_node_num_ptr = (unsigned int *)&child_ptr->sibling_node_num[shifted_search_token & 3];
          if (*next_child_node_num_ptr) {
            child_ptr = &string_nodes[*next_child_node_num_ptr];
            if (search_token == child_ptr->token)
              goto add_string_to_child_match;
            shifted_search_token = shifted_search_token >> 2;
            goto add_string_to_child_check_sibling;
          }
          else { // no matching child so add sibling
add_string_to_child_add_sibling:
            node_data_ptr = (unsigned int *)&string_nodes[*next_string_node_num_ptr];
            *node_data_ptr = *in_token_ptr;
            *(node_data_ptr+1) = (unsigned int)(in_token_ptr - start_token_ptr);
            *((unsigned long long *)node_data_ptr+1) = 0;
            *((unsigned long long *)node_data_ptr+2) = 0;
            *((unsigned long long *)node_data_ptr+3) = 1;
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
        if (in_token_ptr >= match_max_ptr)
          return;
        node_data_ptr = (unsigned int *)&string_nodes[*next_string_node_num_ptr];
        *node_data_ptr = *(start_token_ptr + (size_t)child_ptr->last_match_index + 1);
        *(node_data_ptr+1) = child_ptr->last_match_index + 1;
        *((unsigned long long *)node_data_ptr+1) = 0;
        *((unsigned long long *)node_data_ptr+2) = 0;
        *((unsigned long long *)node_data_ptr+3) = 1;
        child_ptr->child_node_num = *next_string_node_num_ptr;
        *next_string_node_num_ptr += 1;
      }
      if (match_start_index > child_ptr->last_match_index) {
        // increment instances and update last_match_index for strings that do not overlap
        child_ptr->instances++;
        child_ptr->last_match_index = (unsigned int)(in_token_ptr - start_token_ptr);
      }
      child_ptr = &string_nodes[child_ptr->child_node_num];
      search_token = *++in_token_ptr;
      if (search_token == child_ptr->token)
        goto add_string_to_child_match;
      if ((int)search_token >= 0)
        goto add_string_to_child_not_match;
      return;
    }
  }
  else { // first occurence of the token, so create a child
    node_data_ptr = (unsigned int *)&string_nodes[*next_string_node_num_ptr];
    *node_data_ptr = search_token;
    *(node_data_ptr+1) = (unsigned int)(in_token_ptr - start_token_ptr);
    *((unsigned long long *)node_data_ptr+1) = 0;
    *((unsigned long long *)node_data_ptr+2) = 0;
    *((unsigned long long *)node_data_ptr+3) = 1;
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
  unsigned int *node_last_match_ptr;
  unsigned short int num_tokens_in_string, score_index, node_score_num_tokens;
  unsigned short int node_ptrs_num = 0;

  do {
    node_ptr = (struct string_node *)rank_scores_buffer[node_ptrs_num].node_ptrs;
    if ((size_t)node_ptr > 1) {
      d_score = rank_scores_buffer[node_ptrs_num].score;
      if (d_score >= min_score) {
        node_last_match_ptr = start_token_ptr + node_ptr->last_match_index;
        score = (float)d_score;
        // find the position in the score list this node would go in
        unsigned short int score_position, new_score_position, node_scores_search_size;
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
        num_tokens_in_string = rank_scores_buffer[node_ptrs_num].node_num_tokens;
        unsigned int new_score_lmi1, new_score_lmi2, new_score_smi1_m_1, new_score_smi2_m_1;
        // check for overlaps with better score list nodes
        new_score_lmi1 = next_child_ptr->last_match_index - 1;
        new_score_lmi2 = (unsigned int)(node_last_match_ptr - start_token_ptr);

        if (new_score_lmi1 == new_score_lmi2) {
          unsigned int * sibling_node_num_ptr = &next_child_ptr->sibling_node_num[0];
          if (*sibling_node_num_ptr)
            new_score_lmi2 = string_nodes[*sibling_node_num_ptr].last_match_index - 1;
          else if (*(sibling_node_num_ptr + 1))
            new_score_lmi2 = string_nodes[*(sibling_node_num_ptr + 1)].last_match_index - 1;
          else if (*(sibling_node_num_ptr + 2))
            new_score_lmi2 = string_nodes[*(sibling_node_num_ptr + 2)].last_match_index - 1;
          else if (*(sibling_node_num_ptr + 3))
            new_score_lmi2 = string_nodes[*(sibling_node_num_ptr + 3)].last_match_index - 1;
          else {
            new_score_smi1_m_1 = new_score_lmi1 - num_tokens_in_string;
            score_position = 0;
            while (score_position < new_score_position) {
              unsigned int score_last_match_index1;
              score_index = node_scores_index[score_position];
              node_score_num_tokens = node_scores[score_index].num_tokens;
              score_last_match_index1 = node_scores[score_index].last_match_index1;
              if (new_score_lmi1 <= score_last_match_index1 - node_score_num_tokens)
                score_position++;
              else {
                unsigned int score_last_match_index2;
                score_last_match_index2 = node_scores[score_index].last_match_index2;
                if (score_last_match_index2 <= new_score_smi1_m_1)
                  score_position++;
                else if ((score_last_match_index1 <= new_score_smi1_m_1)
                    && (new_score_lmi1 <= score_last_match_index2 - node_score_num_tokens))
                  score_position++;
                else
                  goto rank_scores_thread_node_done;
              }
            }
            // no better overlapping score list nodes, so node will be put on the list
            // look for subsequent overlaps that should be removed (only looks for one to avoid min score reduction)
            if (score_position < num_node_scores) {
              unsigned int eslmi1, eslmi2;
              score_index = node_scores_index[score_position];
              eslmi1 = node_scores[score_index].last_match_index1;
              eslmi2 = node_scores[score_index].last_match_index2;
              node_score_num_tokens = node_scores[score_index].num_tokens;

rank_scores_thread_check_overlap_lmi_equal:
              if ((new_score_lmi1 > eslmi1 - node_score_num_tokens) && (eslmi2 > new_score_smi1_m_1)
                  && ((eslmi1 > new_score_smi1_m_1) || (new_score_lmi1 > eslmi2 - node_score_num_tokens)))
                goto rank_scores_thread_move_down;
              if (++score_position == num_node_scores)
                goto rank_scores_thread_check_max;
              score_index = node_scores_index[score_position];
              eslmi1 = node_scores[score_index].last_match_index1;
              eslmi2 = node_scores[score_index].last_match_index2;
              node_score_num_tokens = node_scores[score_index].num_tokens;
              goto rank_scores_thread_check_overlap_lmi_equal;
            }
          }
        }
        if (new_score_lmi2 < new_score_lmi1) {
          unsigned int temp_lmi = new_score_lmi1;
          new_score_lmi1 = new_score_lmi2;
          new_score_lmi2 = temp_lmi;
        }
        new_score_smi2_m_1 = new_score_lmi2 - num_tokens_in_string;
        new_score_smi1_m_1 = new_score_lmi1 - num_tokens_in_string;
        score_position = 0;
        while (score_position < new_score_position) {
          unsigned int score_last_match_index1;
          score_index = node_scores_index[score_position];
          node_score_num_tokens = node_scores[score_index].num_tokens;
          score_last_match_index1 = node_scores[score_index].last_match_index1;
          if (new_score_lmi2 <= score_last_match_index1 - node_score_num_tokens)
            score_position++;
          else {
            unsigned int score_last_match_index2;
            score_last_match_index2 = node_scores[score_index].last_match_index2;
            if (score_last_match_index2 <= new_score_smi1_m_1)
              score_position++;
            else if (score_last_match_index1 <= new_score_smi2_m_1) {
              if (new_score_lmi1 <= score_last_match_index1 - node_score_num_tokens) {
                if ((new_score_lmi2 <= score_last_match_index2 - node_score_num_tokens)
                    || (score_last_match_index2 <= new_score_smi2_m_1))
                  score_position++;
                else
                  goto rank_scores_thread_node_done;
              }
              else if (score_last_match_index1 <= new_score_smi1_m_1) {
                if (new_score_lmi2 <= score_last_match_index2 - node_score_num_tokens)
                  score_position++;
                else if (score_last_match_index2 <= new_score_smi2_m_1) {
                  if (new_score_lmi1 <= score_last_match_index2 - node_score_num_tokens)
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
          unsigned int eslmi1, eslmi2;
          score_index = node_scores_index[score_position];
          eslmi1 = node_scores[score_index].last_match_index1;
          eslmi2 = node_scores[score_index].last_match_index2;
          node_score_num_tokens = node_scores[score_index].num_tokens;

rank_scores_thread_check_overlap_lmi_not_equal:
          if ((new_score_lmi2 > eslmi1 - node_score_num_tokens)
              && (eslmi2 > new_score_smi1_m_1)
              && ((new_score_lmi1 > eslmi1 - node_score_num_tokens)
                || (eslmi1 > new_score_smi2_m_1)
                || ((new_score_lmi2 > eslmi2 - node_score_num_tokens) && (eslmi2 > new_score_smi2_m_1)))
              && ((eslmi1 > new_score_smi1_m_1)
                || (new_score_lmi1 > eslmi2 - node_score_num_tokens)
                || ((new_score_lmi2 > eslmi2 - node_score_num_tokens) && (eslmi2 > new_score_smi2_m_1))))
            goto rank_scores_thread_move_down;
          if (++score_position == num_node_scores)
            goto rank_scores_thread_check_max;
          score_index = node_scores_index[score_position];
          eslmi1 = node_scores[score_index].last_match_index1;
          eslmi2 = node_scores[score_index].last_match_index2;
          node_score_num_tokens = node_scores[score_index].num_tokens;
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
        node_scores[score_index].num_tokens = num_tokens_in_string;
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
}



void *rank_scores_thread_UTF8_compliant(void *arg)
{
  struct string_node *node_ptr, *next_child_ptr;
  double d_score;
  float score;
  unsigned int *node_last_match_ptr;
  unsigned short int num_tokens_in_string, score_index, node_score_num_tokens;
  unsigned short int node_ptrs_num = 0;

  do {
    node_ptr = (struct string_node *)rank_scores_buffer[node_ptrs_num].node_ptrs;
    if ((size_t)node_ptr > 1) {
      d_score = rank_scores_buffer[node_ptrs_num].score;
      if (d_score >= min_score) {
        node_last_match_ptr = start_token_ptr + node_ptr->last_match_index;
        if ((node_ptr->token == (unsigned int)' ') && (*(node_last_match_ptr-1) != (unsigned int)' ')) {
          d_score *= 0.0625;
          if (d_score < min_score)
            goto rank_scores_thread_UTF8_compliant_node_done;
        }
        else {
          if (node_ptr->token == 'C')
            d_score *= 1.3;
          if (*(node_last_match_ptr - rank_scores_buffer[node_ptrs_num].node_num_tokens) == (unsigned int)'C')
            d_score *= 1.3;
        }
        score = (float)d_score;
        // find the position in the score list this node would go in
        unsigned short int score_position, new_score_position, node_scores_search_size;
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
        num_tokens_in_string = rank_scores_buffer[node_ptrs_num].node_num_tokens;
        unsigned int new_score_lmi1, new_score_lmi2, new_score_smi1_m_1, new_score_smi2_m_1;
        // check for overlaps with better score list nodes
        new_score_lmi1 = next_child_ptr->last_match_index - 1;
        new_score_lmi2 = (unsigned int)(node_last_match_ptr - start_token_ptr);

        if (new_score_lmi1 == new_score_lmi2) {
          unsigned int * sibling_node_num_ptr = &next_child_ptr->sibling_node_num[0];
          if (*sibling_node_num_ptr)
            new_score_lmi2 = string_nodes[*sibling_node_num_ptr].last_match_index - 1;
          else if (*(sibling_node_num_ptr + 1))
            new_score_lmi2 = string_nodes[*(sibling_node_num_ptr + 1)].last_match_index - 1;
          else if (*(sibling_node_num_ptr + 2))
            new_score_lmi2 = string_nodes[*(sibling_node_num_ptr + 2)].last_match_index - 1;
          else if (*(sibling_node_num_ptr + 3))
            new_score_lmi2 = string_nodes[*(sibling_node_num_ptr + 3)].last_match_index - 1;
          else {
            new_score_smi1_m_1 = new_score_lmi1 - num_tokens_in_string;
            score_position = 0;
            while (score_position < new_score_position) {
              unsigned int score_last_match_index1;
              score_index = node_scores_index[score_position];
              node_score_num_tokens = node_scores[score_index].num_tokens;
              score_last_match_index1 = node_scores[score_index].last_match_index1;
              if (new_score_lmi1 <= score_last_match_index1 - node_score_num_tokens)
                score_position++;
              else {
                unsigned int score_last_match_index2;
                score_last_match_index2 = node_scores[score_index].last_match_index2;
                if (score_last_match_index2 <= new_score_smi1_m_1)
                  score_position++;
                else if ((score_last_match_index1 <= new_score_smi1_m_1)
                    && (new_score_lmi1 <= score_last_match_index2 - node_score_num_tokens))
                  score_position++;
                else
                  goto rank_scores_thread_UTF8_compliant_node_done;
              }
            }
            // no better overlapping score list nodes, so node will be put on the list
            // look for subsequent overlaps that should be removed (only looks for one to avoid min score reduction)
            if (score_position < num_node_scores) {
              unsigned int eslmi1, eslmi2;
              score_index = node_scores_index[score_position];
              eslmi1 = node_scores[score_index].last_match_index1;
              eslmi2 = node_scores[score_index].last_match_index2;
              node_score_num_tokens = node_scores[score_index].num_tokens;

rank_scores_thread_UTF8_compliant_check_overlap_lmi_equal:
              if ((new_score_lmi1 > eslmi1 - node_score_num_tokens) && (eslmi2 > new_score_smi1_m_1)
                  && ((eslmi1 > new_score_smi1_m_1) || (new_score_lmi1 > eslmi2 - node_score_num_tokens)))
                goto rank_scores_thread_UTF8_compliant_move_down;
              if (++score_position == num_node_scores)
                goto rank_scores_thread_UTF8_compliant_check_max;
              score_index = node_scores_index[score_position];
              eslmi1 = node_scores[score_index].last_match_index1;
              eslmi2 = node_scores[score_index].last_match_index2;
              node_score_num_tokens = node_scores[score_index].num_tokens;
              goto rank_scores_thread_UTF8_compliant_check_overlap_lmi_equal;
            }
          }
        }
        if (new_score_lmi2 < new_score_lmi1) {
          unsigned int temp_lmi = new_score_lmi1;
          new_score_lmi1 = new_score_lmi2;
          new_score_lmi2 = temp_lmi;
        }
        new_score_smi2_m_1 = new_score_lmi2 - num_tokens_in_string;
        new_score_smi1_m_1 = new_score_lmi1 - num_tokens_in_string;
        score_position = 0;
        while (score_position < new_score_position) {
          unsigned int score_last_match_index1;
          score_index = node_scores_index[score_position];
          node_score_num_tokens = node_scores[score_index].num_tokens;
          score_last_match_index1 = node_scores[score_index].last_match_index1;
          if (new_score_lmi2 <= score_last_match_index1 - node_score_num_tokens)
            score_position++;
          else {
            unsigned int score_last_match_index2;
            score_last_match_index2 = node_scores[score_index].last_match_index2;
            if (score_last_match_index2 <= new_score_smi1_m_1)
              score_position++;
            else if (score_last_match_index1 <= new_score_smi2_m_1) {
              if (new_score_lmi1 <= score_last_match_index1 - node_score_num_tokens) {
                if ((new_score_lmi2 <= score_last_match_index2 - node_score_num_tokens)
                    || (score_last_match_index2 <= new_score_smi2_m_1))
                  score_position++;
                else
                  goto rank_scores_thread_UTF8_compliant_node_done;
              }
              else if (score_last_match_index1 <= new_score_smi1_m_1) {
                if (new_score_lmi2 <= score_last_match_index2 - node_score_num_tokens)
                  score_position++;
                else if (score_last_match_index2 <= new_score_smi2_m_1) {
                  if (new_score_lmi1 <= score_last_match_index2 - node_score_num_tokens)
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
          unsigned int eslmi1, eslmi2;
          score_index = node_scores_index[score_position];
          eslmi1 = node_scores[score_index].last_match_index1;
          eslmi2 = node_scores[score_index].last_match_index2;
          node_score_num_tokens = node_scores[score_index].num_tokens;

rank_scores_thread_UTF8_compliant_check_overlap_lmi_not_equal:
          if ((new_score_lmi2 > eslmi1 - node_score_num_tokens)
              && (eslmi2 > new_score_smi1_m_1)
              && ((new_score_lmi1 > eslmi1 - node_score_num_tokens)
                || (eslmi1 > new_score_smi2_m_1)
                || ((new_score_lmi2 > eslmi2 - node_score_num_tokens) && (eslmi2 > new_score_smi2_m_1)))
              && ((eslmi1 > new_score_smi1_m_1)
                || (new_score_lmi1 > eslmi2 - node_score_num_tokens)
                || ((new_score_lmi2 > eslmi2 - node_score_num_tokens) && (eslmi2 > new_score_smi2_m_1))))
            goto rank_scores_thread_UTF8_compliant_move_down;
          if (++score_position == num_node_scores)
            goto rank_scores_thread_UTF8_compliant_check_max;
          score_index = node_scores_index[score_position];
          eslmi1 = node_scores[score_index].last_match_index1;
          eslmi2 = node_scores[score_index].last_match_index2;
          node_score_num_tokens = node_scores[score_index].num_tokens;
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
        node_scores[score_index].num_tokens = num_tokens_in_string;
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
}



void score_node(struct string_node* node_ptr, double log_expected_match_ratio)
{
  struct string_node *next_child_ptr;
  unsigned short int num_tokens_in_string, level;
  num_tokens_in_string = 2;
  level = 0;

  while (1) {
top_score_loop:
    node_instances = node_ptr->instances;
    if (node_instances >= 2)  {
      node_data[level].log_expected_match_ratio = log_expected_match_ratio;
      log_expected_match_ratio += log_token_count_minus_log_num_tokens[node_ptr->token];
      next_child_ptr = &string_nodes[node_ptr->child_node_num];

      if ((node_instances != next_child_ptr->instances) || (*(start_token_ptr + node_ptr->last_match_index + 1) == 0x20)) {
        // calculate this child's score
        if (node_instances == 2) {
          double delta_match_ratio = log_match_ratios[2] - log_expected_match_ratio;
          double d_score = delta_match_ratio - cutoff_score;
          if (d_score >= 0.0) {
            d_score *= pow((delta_match_ratio - 0.9) * d_num_tokens_in_string_inv[num_tokens_in_string],1.7)
                * (delta_match_ratio + 0.4) * d_num_tokens_in_string_inv[num_tokens_in_string];
            if (d_score >= min_score) {
              if ((node_ptrs_num & 0xFFF) == 0)
                while (rank_scores_buffer[(unsigned short int)(node_ptrs_num + 0x1000)].node_ptrs != 0);
              rank_scores_buffer[node_ptrs_num].score = d_score;
              rank_scores_buffer[node_ptrs_num].node_num_tokens = num_tokens_in_string;
              rank_scores_buffer[node_ptrs_num++].node_ptrs = (size_t)node_ptr;
            }
          }
        }
        else {
          double delta_match_ratio, d_score;
          double d_node_instances_m_1 = (double)(node_instances - 1);
          if (node_instances < NUM_PRECALCULATED_MATCH_RATIO_LOGS)
            delta_match_ratio = log_match_ratios[node_instances] - log_expected_match_ratio;
          else
            delta_match_ratio = log(d_node_instances_m_1 * d_num_token_inv) - log_expected_match_ratio;
          if (delta_match_ratio > 0.9) {
            d_score = d_node_instances_m_1 * delta_match_ratio;
            if (d_score > cutoff_score) {
              d_score -= cutoff_score;
              d_score *= pow((delta_match_ratio - 0.9) * d_num_tokens_in_string_inv[num_tokens_in_string],1.7)
                  * (delta_match_ratio + 0.4) * d_num_tokens_in_string_inv[num_tokens_in_string];
              if (d_score >= min_score) {
                if ((node_ptrs_num & 0xFFF) == 0)
                  while (rank_scores_buffer[(unsigned short int)(node_ptrs_num + 0x1000)].node_ptrs != 0);
                rank_scores_buffer[node_ptrs_num].score = d_score;
                rank_scores_buffer[node_ptrs_num].node_num_tokens = num_tokens_in_string;
                rank_scores_buffer[node_ptrs_num++].node_ptrs = (size_t)node_ptr;
              }
            }
          }
        }
      }
      node_data[level].node_ptr = node_ptr;
      node_data[level].num_tokens_in_string = num_tokens_in_string++;
      node_data[level++].next_sibling = 0;
      node_ptr = next_child_ptr;
      goto top_score_loop;
    }

    unsigned int sib_node_num = node_ptr->sibling_node_num[0];
    if (sib_node_num == 0) {
      sib_node_num = node_ptr->sibling_node_num[1];
      if (sib_node_num == 0) {
        sib_node_num = node_ptr->sibling_node_num[2];
        if (sib_node_num == 0) {
          sib_node_num = node_ptr->sibling_node_num[3];
          if (sib_node_num == 0) {
            while (level--) {
              unsigned char sibling_number = node_data[level].next_sibling;
              node_ptr = node_data[level].node_ptr;
              if (sibling_number != 3) {
                if (sibling_number != 2) {
                  if (sibling_number == 0) {
                    if (node_ptr->sibling_node_num[0]) {
                      node_ptr = &string_nodes[node_ptr->sibling_node_num[0]];
                      num_tokens_in_string = node_data[level].num_tokens_in_string;
                      log_expected_match_ratio = node_data[level].log_expected_match_ratio;
                      node_data[level++].next_sibling = 1;
                      goto top_score_loop;
                    }
                  }
                  if (node_ptr->sibling_node_num[1]) {
                    node_ptr = &string_nodes[node_ptr->sibling_node_num[1]];
                    num_tokens_in_string = node_data[level].num_tokens_in_string;
                    log_expected_match_ratio = node_data[level].log_expected_match_ratio;
                    node_data[level++].next_sibling = 2;
                    goto top_score_loop;
                  }
                }
                if (node_ptr->sibling_node_num[2]) {
                  node_ptr = &string_nodes[node_ptr->sibling_node_num[2]];
                  num_tokens_in_string = node_data[level].num_tokens_in_string;
                  log_expected_match_ratio = node_data[level].log_expected_match_ratio;
                  node_data[level++].next_sibling = 3;
                  goto top_score_loop;
                }
              }
              if (node_ptr->sibling_node_num[3]) {
                node_ptr = &string_nodes[node_ptr->sibling_node_num[3]];
                num_tokens_in_string = node_data[level].num_tokens_in_string;
                log_expected_match_ratio = node_data[level].log_expected_match_ratio;
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
          node_data[level].num_tokens_in_string = num_tokens_in_string;
          node_data[level].log_expected_match_ratio = log_expected_match_ratio;
          node_data[level++].next_sibling = 3;
          node_ptr = &string_nodes[sib_node_num];
        }
      }
      else {
        node_data[level].node_ptr = node_ptr;
        node_data[level].num_tokens_in_string = num_tokens_in_string;
        node_data[level].log_expected_match_ratio = log_expected_match_ratio;
        node_data[level++].next_sibling = 2;
        node_ptr = &string_nodes[sib_node_num];
      }
    }
    else {
      node_data[level].node_ptr = node_ptr;
      node_data[level].num_tokens_in_string = num_tokens_in_string;
      node_data[level].log_expected_match_ratio = log_expected_match_ratio;
      node_data[level++].next_sibling = 1;
      node_ptr = &string_nodes[sib_node_num];
    }
  }
}



void *build_lcp_thread(void *arg)
{
  struct lcp_thread_data *thread_data_ptr;
  unsigned int min_token, max_token;
  unsigned int next_string_node_num, string_node_num_limit;
  unsigned int *in_token_ptr, *recent_stop_token_ptr;

  thread_data_ptr = (struct lcp_thread_data *)arg;
  in_token_ptr = (unsigned int *)min_token_ptr;
  min_token = thread_data_ptr->min_token;
  max_token = thread_data_ptr->max_token;
  next_string_node_num = thread_data_ptr->first_string_node_num;
  string_node_num_limit = thread_data_ptr->string_nodes_limit - MAX_STRING_LENGTH;

  while ((unsigned int * volatile)max_token_ptr != in_token_ptr) {
    recent_stop_token_ptr = (unsigned int *)stop_token_ptr;
    while (in_token_ptr != recent_stop_token_ptr) {
      if (next_string_node_num < string_node_num_limit) {
        unsigned int this_token;
        this_token = *in_token_ptr++;
        if ((this_token >= min_token) && (this_token <= max_token))
          add_suffix(this_token,in_token_ptr,&next_string_node_num);
      }
      else
        in_token_ptr = recent_stop_token_ptr;
    }
    thread_data_ptr->current_token_ptr = in_token_ptr;
  }
}



#define score_nodes(max_token) \
{ \
  while (i1 <= max_token) { \
    if (*base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],log_token_count_minus_log_num_tokens[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],log_token_count_minus_log_num_tokens[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],log_token_count_minus_log_num_tokens[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],log_token_count_minus_log_num_tokens[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],log_token_count_minus_log_num_tokens[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],log_token_count_minus_log_num_tokens[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],log_token_count_minus_log_num_tokens[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],log_token_count_minus_log_num_tokens[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],log_token_count_minus_log_num_tokens[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],log_token_count_minus_log_num_tokens[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],log_token_count_minus_log_num_tokens[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],log_token_count_minus_log_num_tokens[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],log_token_count_minus_log_num_tokens[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],log_token_count_minus_log_num_tokens[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],log_token_count_minus_log_num_tokens[i1]); \
    if (*++base_node_child_num_ptr) \
      score_node(&string_nodes[*base_node_child_num_ptr],log_token_count_minus_log_num_tokens[i1]); \
    ++base_node_child_num_ptr; \
    i1++; \
  } \
  while (rank_scores_buffer[node_ptrs_num].node_ptrs != 0); \
}



void *overlap_check_thread(void *arg)
{
  struct overlap_check_data *thread_data_ptr;
  struct match_node *match_node_ptr;
  unsigned int this_token, prior_match_score_number[MAX_PRIOR_MATCHES];
  unsigned int *prior_match_end_ptr[MAX_PRIOR_MATCHES];
  unsigned int *in_token_ptr;
  unsigned int *end_token_ptr;
  unsigned int num_prior_matches = 0;

  thread_data_ptr = (struct overlap_check_data *)arg;
  in_token_ptr = thread_data_ptr->start_token_ptr;
  end_token_ptr = thread_data_ptr->stop_token_ptr;

thread_overlap_check_loop_no_match:
  if (in_token_ptr == end_token_ptr)
    goto thread_overlap_check_loop_end;
  this_token = *in_token_ptr++;
  if ((int)this_token < 0)
    goto thread_overlap_check_loop_no_match;
  if (match_nodes[this_token].num_tokens == 0)
    goto thread_overlap_check_loop_no_match;
  match_node_ptr = &match_nodes[this_token];

thread_overlap_check_loop_match:
  if (in_token_ptr == end_token_ptr)
    goto thread_overlap_check_loop_end;
  this_token = *in_token_ptr++;
  if ((int)this_token < 0)
    goto thread_overlap_check_loop_no_match;
  match_node_ptr = match_node_ptr->child_ptr;
  if (this_token != match_node_ptr->token) {
    unsigned int shifted_token = this_token;
    do {
      if (match_node_ptr->sibling_node_num[shifted_token & 0xF] != 0) {
        match_node_ptr = &match_nodes[match_node_ptr->sibling_node_num[shifted_token & 0xF]];
        shifted_token = shifted_token >> 4;
      }
      else {
        if (match_node_ptr->miss_ptr == 0) {
          if (match_nodes[this_token].num_tokens == 0)
            goto thread_overlap_check_loop_no_match;
          match_node_ptr = &match_nodes[this_token];
          goto thread_overlap_check_loop_match;
        }
        else {
          match_node_ptr = match_node_ptr->miss_ptr;
          shifted_token = this_token;
        }
      }
    } while (this_token != match_node_ptr->token);
  }
  if (match_node_ptr->child_ptr)
    goto thread_overlap_check_loop_match;

  // no child, so found a match - check for overlaps
  unsigned int i1;
  unsigned char found_same_score_prior_match = 0;
  unsigned int node_score_number = match_node_ptr->score_number;
  unsigned int prior_match_number = 0;
  while (prior_match_number < num_prior_matches) {
    if (in_token_ptr - match_node_ptr->num_tokens > prior_match_end_ptr[prior_match_number]) {
      num_prior_matches--;
      for (i1 = prior_match_number ; i1 < num_prior_matches ; i1++) {
        prior_match_end_ptr[i1] = prior_match_end_ptr[i1+1];
        prior_match_score_number[i1] = prior_match_score_number[i1+1];
      }
    }
    else { // overlapping token substitution strings, so invalidate the lower score
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
    prior_match_end_ptr[num_prior_matches] = in_token_ptr - 1;
    prior_match_score_number[num_prior_matches++] = node_score_number;
  }
  if (match_node_ptr == 0)
    goto thread_overlap_check_loop_no_match;
  else
    goto thread_overlap_check_loop_match;

thread_overlap_check_loop_end:
  match_node_ptr = 0;
}



void *substitute_thread(void *arg)
{
  unsigned int * end_data_ptr;
  unsigned int * near_end_data_ptr;
  unsigned int data = 0;
  unsigned short int substitute_data_index = 0;
  unsigned int * old_data_ptr = start_token_ptr;

  while (data != 0xFFFFFFFF) {
    if (data) {
      if ((int)data > 0) {
substitute_copy:
        end_data_ptr = out_token_ptr + data;
        near_end_data_ptr = end_data_ptr - 32;
        while (out_token_ptr < near_end_data_ptr) {
          *(unsigned long long *)out_token_ptr = *(unsigned long long *)old_data_ptr;
          *((unsigned long long *)out_token_ptr + 1) = *((unsigned long long *)old_data_ptr + 1);
          *((unsigned long long *)out_token_ptr + 2) = *((unsigned long long *)old_data_ptr + 2);
          *((unsigned long long *)out_token_ptr + 3) = *((unsigned long long *)old_data_ptr + 3);
          *((unsigned long long *)out_token_ptr + 4) = *((unsigned long long *)old_data_ptr + 4);
          *((unsigned long long *)out_token_ptr + 5) = *((unsigned long long *)old_data_ptr + 5);
          *((unsigned long long *)out_token_ptr + 6) = *((unsigned long long *)old_data_ptr + 6);
          *((unsigned long long *)out_token_ptr + 7) = *((unsigned long long *)old_data_ptr + 7);
          *((unsigned long long *)out_token_ptr + 8) = *((unsigned long long *)old_data_ptr + 8);
          *((unsigned long long *)out_token_ptr + 9) = *((unsigned long long *)old_data_ptr + 9);
          *((unsigned long long *)out_token_ptr + 10) = *((unsigned long long *)old_data_ptr + 10);
          *((unsigned long long *)out_token_ptr + 11) = *((unsigned long long *)old_data_ptr + 11);
          *((unsigned long long *)out_token_ptr + 12) = *((unsigned long long *)old_data_ptr + 12);
          *((unsigned long long *)out_token_ptr + 13) = *((unsigned long long *)old_data_ptr + 13);
          *((unsigned long long *)out_token_ptr + 14) = *((unsigned long long *)old_data_ptr + 14);
          *((unsigned long long *)out_token_ptr + 15) = *((unsigned long long *)old_data_ptr + 15);
          old_data_ptr += 32;
          out_token_ptr += 32;
        }
        while (out_token_ptr < end_data_ptr - 1) {
          *(unsigned long long *)out_token_ptr = *(unsigned long long *)old_data_ptr;
          old_data_ptr += 2;
          out_token_ptr += 2;
        }
        while (out_token_ptr != end_data_ptr)
          *out_token_ptr++ = *old_data_ptr++;
        substitute_data[substitute_data_index++] = 0;
        data = substitute_data[substitute_data_index];
        if ((int)data < (int)0xFFFFFFFF)
          goto substitute_new_token;
      }
      else {
substitute_new_token:
        substitute_data[substitute_data_index++] = 0;
        old_data_ptr += (size_t)(data - 0x80000000);
        while (substitute_data[substitute_data_index] == 0);
        unsigned int symbol = substitute_data[substitute_data_index];
        token_count[symbol]++;
        *out_token_ptr++ = symbol; 
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
}




void *find_substitutions_thread(void *arg)
{
  struct match_node *match_node_ptr;
  unsigned int this_token, node_score_number;
  struct find_substitutions_data * thread_data_ptr = (struct find_substitutions_data *)arg;
  unsigned int * in_token_ptr = (unsigned int *)thread_data_ptr->start_token_ptr;
  unsigned int * end_token_ptr = thread_data_ptr->stop_token_ptr;
  unsigned int substitute_index = 0;
  unsigned int num_tokens_to_copy = 0;

  thread_data_ptr->extra_match_symbols = 0;
  if (in_token_ptr == end_token_ptr)
    goto thread_token_substitution_loop_end;
  this_token = *in_token_ptr++;
  if ((int)this_token >= 0) {
thread_token_substitution_loop_no_match_with_symbol:
    match_node_ptr = &match_nodes[this_token];
    if (match_node_ptr->num_tokens) {
      this_token = *in_token_ptr++;
      if ((int)this_token >= 0) {
        if (match_node_ptr->child_ptr == 0) {
          if (num_tokens_to_copy >= 100000) {
            if (substitute_index == 0x400000) {
              thread_data_ptr->num_substitutions += 0x400000;
              substitute_index = 0;
              while (thread_data_ptr->data[0x3FFFFF]);
            }
            thread_data_ptr->data[substitute_index++] = num_tokens_to_copy;
            num_tokens_to_copy = 0;
          }
          if (in_token_ptr == end_token_ptr)
            goto thread_token_substitution_loop_end;
          this_token = *in_token_ptr++;
          if ((int)this_token >= 0)
            goto thread_token_substitution_loop_no_match_with_symbol;
          num_tokens_to_copy++;
          if (in_token_ptr == end_token_ptr)
            goto thread_token_substitution_loop_end;
          this_token = *in_token_ptr++;
          goto thread_token_substitution_loop_no_match_with_symbol;
        }
thread_token_substitution_loop_match_with_child:
        match_node_ptr = match_node_ptr->child_ptr;
        if (this_token != match_node_ptr->token) {
          unsigned int sibling_nibble = this_token;
          do {
            if (match_node_ptr->sibling_node_num[sibling_nibble & 0xF]) {
              match_node_ptr = &match_nodes[match_node_ptr->sibling_node_num[sibling_nibble & 0xF]];
              sibling_nibble = sibling_nibble >> 4;
            }
            else { // no match, so use miss node and output missed tokens
              if (match_node_ptr->miss_ptr == 0) {
                if (match_nodes[this_token].num_tokens) {
                  if (in_token_ptr > end_token_ptr) {
                    num_tokens_to_copy += match_node_ptr->num_tokens - (in_token_ptr - end_token_ptr);
                    goto thread_token_substitution_loop_end;
                  }
                  sibling_nibble = sibling_nibble >> 4;
                  num_tokens_to_copy += match_node_ptr->num_tokens - 1;
                  match_node_ptr = &match_nodes[this_token];
                }
                else {
                  if (in_token_ptr >= end_token_ptr) {
                    num_tokens_to_copy += match_node_ptr->num_tokens - (in_token_ptr - end_token_ptr);
                    goto thread_token_substitution_loop_end;
                  }
                  num_tokens_to_copy += match_node_ptr->num_tokens;
                  if (num_tokens_to_copy >= 100000) {
                    if (substitute_index == 0x400000) {
                      thread_data_ptr->num_substitutions += 0x400000;
                      substitute_index = 0;
                      while (thread_data_ptr->data[0x3FFFFF]);
                    }
                    thread_data_ptr->data[substitute_index++] = num_tokens_to_copy;
                    num_tokens_to_copy = 0;
                  }
                  if (in_token_ptr == end_token_ptr)
                    goto thread_token_substitution_loop_end;
                  this_token = *in_token_ptr++;
                  if ((int)this_token >= 0)
                    goto thread_token_substitution_loop_no_match_with_symbol;
                  num_tokens_to_copy++;
                  if (in_token_ptr == end_token_ptr)
                    goto thread_token_substitution_loop_end;
                  this_token = *in_token_ptr++;
                  goto thread_token_substitution_loop_no_match_with_symbol;
                }
              }
              else {
                num_tokens_to_copy += match_node_ptr->num_tokens - match_node_ptr->miss_ptr->num_tokens;
                if (in_token_ptr - match_node_ptr->miss_ptr->num_tokens >= end_token_ptr) {
                  num_tokens_to_copy -= in_token_ptr - end_token_ptr - match_node_ptr->miss_ptr->num_tokens;
                  goto thread_token_substitution_loop_end;
                }
                match_node_ptr = match_node_ptr->miss_ptr;
                sibling_nibble = this_token;
              }
            }
          } while (this_token != match_node_ptr->token);
        }
        if (match_node_ptr->child_ptr == 0) { // no child, so found a match
          if (num_tokens_to_copy) {
            if (substitute_index == 0x400000) {
              thread_data_ptr->num_substitutions += 0x400000;
              substitute_index = 0;
              while (thread_data_ptr->data[0x3FFFFF]);
            }
            thread_data_ptr->data[substitute_index++] = num_tokens_to_copy;
            num_tokens_to_copy = 0;
          }
          node_score_number = match_node_ptr->score_number;
          if (substitute_index == 0x400000) {
            thread_data_ptr->num_substitutions += 0x400000;
            substitute_index = 0;
            while (thread_data_ptr->data[0x3FFFFF]);
          }
          thread_data_ptr->data[substitute_index++] = 0x80000000 + match_node_ptr->num_tokens;
          if (substitute_index == 0x400000) {
            thread_data_ptr->num_substitutions += 0x400000;
            substitute_index = 0;
            while (thread_data_ptr->data[0x3FFFFF]);
          }
          thread_data_ptr->data[substitute_index++] = num_base_tokens + new_token_number[node_score_number];
          if (in_token_ptr >= end_token_ptr) {
            thread_data_ptr->extra_match_symbols = in_token_ptr - end_token_ptr;
            goto thread_token_substitution_loop_end;
          }
          this_token = *in_token_ptr++;
          if ((int)this_token >= 0)
            goto thread_token_substitution_loop_no_match_with_symbol;
          num_tokens_to_copy++;
          if (in_token_ptr == end_token_ptr)
            goto thread_token_substitution_loop_end;
          this_token = *in_token_ptr++;
          goto thread_token_substitution_loop_no_match_with_symbol;
        }
        if (num_tokens_to_copy >= 100000) {
          if (substitute_index == 0x400000) {
            thread_data_ptr->num_substitutions += 0x400000;
            substitute_index = 0;
            while (thread_data_ptr->data[0x3FFFFF]);
          }
          thread_data_ptr->data[substitute_index++] = num_tokens_to_copy;
          num_tokens_to_copy = 0;
        }
        this_token = *in_token_ptr++;
        if ((int)this_token >= 0)
          goto thread_token_substitution_loop_match_with_child;
        num_tokens_to_copy += match_node_ptr->num_tokens + 1;
        if (in_token_ptr >= end_token_ptr) {
          num_tokens_to_copy -= in_token_ptr - end_token_ptr;
          goto thread_token_substitution_loop_end;
        }
        this_token = *in_token_ptr++;
        goto thread_token_substitution_loop_no_match_with_symbol;
      }
      else { // define token
        num_tokens_to_copy += match_node_ptr->num_tokens + 1;
        if (in_token_ptr >= end_token_ptr) {
          num_tokens_to_copy -= in_token_ptr - end_token_ptr;
          goto thread_token_substitution_loop_end;
        }
        this_token = *in_token_ptr++;
        goto thread_token_substitution_loop_no_match_with_symbol;
      }
    }
    if (++num_tokens_to_copy <= 100000) {
      if (in_token_ptr == end_token_ptr)
        goto thread_token_substitution_loop_end;
      this_token = *in_token_ptr++;
      if ((int)this_token >= 0)
        goto thread_token_substitution_loop_no_match_with_symbol;
      num_tokens_to_copy++;
      if (in_token_ptr == end_token_ptr)
        goto thread_token_substitution_loop_end;
      this_token = *in_token_ptr++;
      goto thread_token_substitution_loop_no_match_with_symbol;
    }
    if (substitute_index == 0x400000) {
      thread_data_ptr->num_substitutions += 0x400000;
      substitute_index = 0;
      while (thread_data_ptr->data[0x3FFFFF]);
    }
    thread_data_ptr->data[substitute_index++] = num_tokens_to_copy;
    num_tokens_to_copy = 0;
    if (in_token_ptr == end_token_ptr)
      goto thread_token_substitution_loop_end;
    this_token = *in_token_ptr++;
    if ((int)this_token >= 0)
      goto thread_token_substitution_loop_no_match_with_symbol;
    num_tokens_to_copy = 1;
    if (in_token_ptr == end_token_ptr)
      goto thread_token_substitution_loop_end;
    this_token = *in_token_ptr++;
    goto thread_token_substitution_loop_no_match_with_symbol;
  }
  else { // define token
    num_tokens_to_copy++;
    if (in_token_ptr == end_token_ptr)
      goto thread_token_substitution_loop_end;
    this_token = *in_token_ptr++;
    goto thread_token_substitution_loop_no_match_with_symbol;
  }

thread_token_substitution_loop_end:
  if (num_tokens_to_copy) {
    if (substitute_index == 0x400000) {
      thread_data_ptr->num_substitutions += 0x400000;
      substitute_index = 0;
      while (thread_data_ptr->data[0x3FFFFF]);
    }
    thread_data_ptr->data[substitute_index++] = num_tokens_to_copy;
  }
  thread_data_ptr->num_substitutions += substitute_index;
  thread_data_ptr->done = 1;
}



int main(int argc, char* argv[])
{
  FILE *fd_in, *fd_out;
  size_t available_RAM;
  unsigned int in_size, num_in_tokens, num_start_tokens, num_tokens_defined, arg_num, i2;
  unsigned int best_score_num_chars, UTF8_value, max_UTF8_value, num_tokens_processed, token, num_tokens_to_copy;
  unsigned int first_token_number, node_score_number, suffix_node_number, next_string_node_num, string_node_num_limit;
  unsigned int *search_match_ptr, *match_strings, *match_string_start_ptr, *node_string_start_ptr;
  unsigned short int scan_cycle, num_tokens_in_string;
  unsigned char UTF8_compliant, cap_encoded, user_set_RAM_size, this_char, delta_gap;
  unsigned char *free_RAM_ptr, *write_ptr;
  unsigned char out_char, out_file_name[50];
  double d_num_token, prior_min_score, new_min_score, order_0_entropy, d_token_count, this_log_token_count_minus_log_num_token;
  double log_num_token, log2_inv, RAM_usage;
  float prior_cycle_start_ratio, prior_cycle_end_ratio, estimated_nodes_per_token;
  struct string_node *string_node_ptr;

  pthread_t build_lcp_thread1, build_lcp_thread2, build_lcp_thread3, build_lcp_thread4, build_lcp_thread5, build_lcp_thread6;
  pthread_t rank_scores_thread1, substitute_thread1;
  pthread_t overlap_check_threads[7];
  pthread_t find_substitutions_threads[7];

  unsigned long long start_time = (unsigned long long)clock();

  log2_inv = 1.0/log(2.0);
  for (i1 = 0 ; i1 < MAX_STRING_LENGTH ; i1++)
    d_num_tokens_in_string_inv[i1] = 1.0 / (double)i1;

  for (i1 = 0 ; i1 < MAX_SCORES ; i1++)
    node_scores_bad[i1] = 0;

  for (i1 = 0 ; i1 < 0x10000 ; i1++)
    substitute_data[i1] = 0;

  cutoff_score = 4.5;
  RAM_usage = 6.5;
  user_set_RAM_size = 0;
  arg_num = 1;
  while (*argv[arg_num] ==  '-') {
    if (*(argv[arg_num]+1) == 'm')
      cutoff_score = (double)atof(argv[arg_num++]+2);
    else if (*(argv[arg_num]+1) == 'r') {
      user_set_RAM_size = 1;
      RAM_usage = (double)atof(argv[arg_num++]+2);
      if (RAM_usage < 5.0) {
        fprintf(stderr,"ERROR: -r value must be >= 5.0\n");
        exit(0);
      }
    }
    else {
      fprintf(stderr,"ERROR - Invalid '-' format.  Only -m<value> and -r<value> allowed\n");
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
  if (user_set_RAM_size) {
    available_RAM = (size_t)((double)in_size * RAM_usage) + 30000000;
    if (available_RAM > MAX_MEMORY_USAGE)
      available_RAM = MAX_MEMORY_USAGE;
  }
  else if (in_size > 260000000)
    if (13 * (size_t)in_size / 2 < MAX_MEMORY_USAGE)
      available_RAM = 13 * (size_t)in_size / 2;
    else
      available_RAM = MAX_MEMORY_USAGE;
  else
    available_RAM = 1690000000;
    

  start_token_ptr = (unsigned int *)malloc(available_RAM + 100000000 + 4 * in_size);
  if (start_token_ptr == 0) {
    fprintf(stderr,"ERROR - Insufficient RAM to compress - unable to allocate %Iu bytes for nodes\n",
      available_RAM + 100000000 + 4 * (size_t)in_size);
    exit(0);
  }
  fprintf(stderr,"Allocated %Iu bytes for data processing\n",available_RAM);

  char_buffer = (unsigned char *)start_token_ptr + 4 * (in_size + 1);
  in_token_ptr = start_token_ptr;

  i1 = fread(char_buffer,1,in_size,fd_in);
  fflush(fd_in);
  fclose(fd_in);
  fprintf(stderr,"Read %u byte input file\n",i1);

  // parse the file to determine UTF8_compliant
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
    if (*in_char_ptr >= INSERT_TOKEN_CHAR) {
      if (*(in_char_ptr+1) != DEFINE_TOKEN_CHAR)
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

  fprintf(stderr,"cap encoded: %u, UTF8 compliant %u\n",cap_encoded,UTF8_compliant);

  // parse the file to determine num_tokens_defined and max_UTF8_value
  num_in_tokens = 0;
  num_tokens_defined = 0;
  in_char_ptr = char_buffer + 1;

  if (UTF8_compliant) {
    num_base_tokens = START_MY_TOKENS;
    first_token_number = 0x80000000 + START_MY_TOKENS;
    max_UTF8_value = 0;
    while (in_char_ptr != end_char_ptr) {
      this_char = *in_char_ptr++;
      if (this_char < 0x80)
        *in_token_ptr++ = (unsigned int)this_char;
      else if (this_char == INSERT_TOKEN_CHAR) {
        *in_token_ptr++ = START_MY_TOKENS + 0x10000 * (unsigned int)*in_char_ptr
            + 0x100 * (unsigned int)*(in_char_ptr+1) + (unsigned int)*(in_char_ptr+2);
        in_char_ptr += 3;
      }
      else if (this_char == DEFINE_TOKEN_CHAR) {
        *in_token_ptr++ = first_token_number + 0x10000 * (unsigned int)*in_char_ptr
            + 0x100 * (unsigned int)*(in_char_ptr+1) + (unsigned int)*(in_char_ptr+2);
        in_char_ptr += 3;
        num_tokens_defined++;
      }
      else if (this_char >= 0x80) {
        if (this_char >= 0xF0) {
          UTF8_value = 0x40000 * (unsigned int)(this_char & 0x7) + 0x1000 * (unsigned int)(*in_char_ptr++ & 0x3F);
          UTF8_value += 0x40 * (unsigned int)(*in_char_ptr++ & 0x3F);
          UTF8_value += (unsigned int)*in_char_ptr++ & 0x3F;
        }
        else if (this_char >= 0xE0) {
          UTF8_value = 0x1000 * (unsigned int)(this_char & 0xF) + 0x40 * (unsigned int)(*in_char_ptr++ & 0x3F);
          UTF8_value += (unsigned int)*in_char_ptr++ & 0x3F;
        }
        else 
          UTF8_value = 0x40 * (unsigned int)(this_char & 0x1F) + (*in_char_ptr++ & 0x3F);
        if (UTF8_value > max_UTF8_value)
          max_UTF8_value = UTF8_value;
        *in_token_ptr++ = UTF8_value;
      }
      num_in_tokens++;
    }
    fprintf(stderr,"Found %u symbols, %u defines, maximum unicode value 0x%x\n",num_in_tokens,num_tokens_defined,max_UTF8_value);
  }
  else {
    available_RAM += 4 * (size_t)in_size;
    num_base_tokens = 0x100;
    first_token_number = 0x80000000 + 0x100;
    while (in_char_ptr != end_char_ptr) {
      this_char = *in_char_ptr++;
      if (this_char < INSERT_TOKEN_CHAR)
        *in_token_ptr++ = (unsigned int)this_char;
      else {
        if (*in_char_ptr == DEFINE_TOKEN_CHAR) {
          *in_token_ptr++ = (unsigned int)this_char;
          in_char_ptr++;
        }
        else {
          if (this_char == INSERT_TOKEN_CHAR)
            *in_token_ptr++ = 0x100 + 0x10000 * (unsigned int)*in_char_ptr
                + 0x100 * (unsigned int)*(in_char_ptr+1) + (unsigned int)*(in_char_ptr+2);
          else {
            *in_token_ptr++ = first_token_number + 0x10000 * (unsigned int)*in_char_ptr
                + 0x100 * (unsigned int)*(in_char_ptr+1) + (unsigned int)*(in_char_ptr+2);
            num_tokens_defined++;
          }
          in_char_ptr += 3;
        }
      }
      num_in_tokens++;
    }
    fprintf(stderr,"Found %u symbols, %u defines\n",num_in_tokens,num_tokens_defined);
  }
  end_token_ptr = in_token_ptr;
  *end_token_ptr = 0xFFFFFFFE;
  free_RAM_ptr = (unsigned char *)(end_token_ptr + 1);
  available_RAM = (available_RAM / 20) * 19;

  unsigned long long *token_count_ptr;
  token_count_ptr = (unsigned long long *)token_count;
  while (token_count_ptr < (unsigned long long *)(token_count + num_start_tokens))
    *token_count_ptr++ = 0;

  // parse the data to determine token_counts
  in_token_ptr = start_token_ptr;
  do {
    token = *in_token_ptr++;
    while ((int)token >= 0) {
      token_count[token]++;
      token = *in_token_ptr++;
    }
  } while (token != 0xFFFFFFFE);

  log_instances[1] = 0.0;
  for (i1=2 ; i1<NUM_PRECALCULATED_INSTANCE_LOGS ; i1++)
    log_instances[i1] = log((double)i1);

  i1 = 0x10000;
  while (i1--)
    rank_scores_buffer[i1].node_ptrs = 0;

  max_scores = 6000;
  min_score = cutoff_score;
  prior_min_score = min_score;
  prior_cycle_start_ratio = 0.0;
  prior_cycle_end_ratio = 1.0;
  scan_cycle = 0;

  do {
    num_start_tokens = num_base_tokens + num_tokens_defined;
    num_in_tokens = end_token_ptr - start_token_ptr;
    *end_token_ptr = 0xFFFFFFFE;

    // Allocate memory for the log token count arrays
    if ((size_t)free_RAM_ptr % sizeof(double) != 0)
      free_RAM_ptr = (unsigned char *)(((size_t)free_RAM_ptr/sizeof(double) + 1) * sizeof(double));
    log_token_count_minus_log_num_tokens = (double *)free_RAM_ptr;
    free_RAM_ptr += sizeof(double) * (size_t)num_start_tokens;

    // Set the memory addresses for the base_string_nodes_child_ptr array
    base_string_nodes_child_node_num = (unsigned int *)free_RAM_ptr;

    // pre-calculate log match ratios
    d_num_token = (double)num_in_tokens;
    d_num_token_inv = 1.0 / d_num_token;
    for (i1=2 ; i1<NUM_PRECALCULATED_MATCH_RATIO_LOGS ; i1++)
      log_match_ratios[i1] = log((double)(i1-1) * d_num_token_inv);  // offset by 1 because the first instance is not a match

    order_0_entropy = 0.0;
    log_num_token = log(d_num_token);
    i1 = 0;

    do {
      if (token_count[i1] != 0) {
        if (token_count[i1] < NUM_PRECALCULATED_INSTANCE_LOGS) {
          this_log_token_count_minus_log_num_token = log_instances[token_count[i1]] - log_num_token;
          log_token_count_minus_log_num_tokens[i1] = this_log_token_count_minus_log_num_token;
          order_0_entropy -= (double)token_count[i1] * this_log_token_count_minus_log_num_token;
        }
        else {
          d_token_count = (double)token_count[i1];
          this_log_token_count_minus_log_num_token = log(d_token_count) - log_num_token;
          log_token_count_minus_log_num_tokens[i1] = this_log_token_count_minus_log_num_token;
          order_0_entropy -= d_token_count * this_log_token_count_minus_log_num_token;
        }
      }
    } while (++i1 < num_base_tokens);

    if (num_tokens_defined != 0) {
      while (i1 < num_start_tokens) {
        if (token_count[i1] < NUM_PRECALCULATED_INSTANCE_LOGS) {
          this_log_token_count_minus_log_num_token = log_instances[token_count[i1]] - log_num_token;
          log_token_count_minus_log_num_tokens[i1] = this_log_token_count_minus_log_num_token;
          order_0_entropy -= (double)token_count[i1++] * this_log_token_count_minus_log_num_token;
        }
        else {
          d_token_count = (double)token_count[i1];
          this_log_token_count_minus_log_num_token = log(d_token_count) - log_num_token;
          log_token_count_minus_log_num_tokens[i1++] = this_log_token_count_minus_log_num_token;
          order_0_entropy -= d_token_count * this_log_token_count_minus_log_num_token;
        }
      }
      d_token_count = (double)num_tokens_defined;
      this_log_token_count_minus_log_num_token = log(d_token_count) - log_num_token;
      order_0_entropy -= d_token_count * this_log_token_count_minus_log_num_token;
    }
    order_0_entropy *= log2_inv * d_num_token_inv;
    fprintf(stderr,"%u: %u syms, dict. size %u, %.4f bits/sym, o0e %u bytes\n",
        ++scan_cycle,num_in_tokens,num_tokens_defined,order_0_entropy,(unsigned int)(d_num_token*order_0_entropy/8.0));

    // setup to build the suffix tree
    unsigned long long *base_node_ptr = (unsigned long long *)base_string_nodes_child_node_num;
    while (base_node_ptr < (unsigned long long *)(base_string_nodes_child_node_num
        + (num_start_tokens * BASE_NODES_CHILD_ARRAY_SIZE))) {
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
    num_tokens_processed = 0;
    num_node_scores = 0;

    // Set the memory adddress for the suffix tree nodes
    string_nodes = (struct string_node *)((size_t)free_RAM_ptr
        + sizeof(unsigned int) * (size_t)num_start_tokens * BASE_NODES_CHILD_ARRAY_SIZE);
    string_node_num_limit = (unsigned int)(((size_t)start_token_ptr + available_RAM - (size_t)string_nodes)
        / sizeof(struct string_node)) - MAX_STRING_LENGTH;

    if (1.0 - prior_cycle_end_ratio < prior_cycle_end_ratio - prior_cycle_start_ratio) {
      if ((1.0 - prior_cycle_end_ratio) * 1.5 < prior_cycle_end_ratio - prior_cycle_start_ratio) {
        prior_cycle_start_ratio = 0.0;
        in_token_ptr = start_token_ptr;
      }
      else {
        prior_cycle_start_ratio = 1.0 - 0.95 * (prior_cycle_end_ratio - prior_cycle_start_ratio);
        in_token_ptr = start_token_ptr + (unsigned int)(prior_cycle_start_ratio * (float)(end_token_ptr - start_token_ptr));
      }
    }
    else {
      prior_cycle_start_ratio = prior_cycle_end_ratio;
      in_token_ptr = start_token_ptr + (unsigned int)(prior_cycle_start_ratio * (float)(end_token_ptr - start_token_ptr));
    }

    next_string_node_num = 0;
    fprintf(stderr,"Common prefix scan 0 - %x\r",num_start_tokens-1);

    unsigned int sum_symbols, symbols_limit; 
    unsigned int main_max_token;
    unsigned int main_string_nodes_limit;
    i1 = 1;
    sum_symbols = token_count[0];
    symbols_limit = ((num_in_tokens - num_tokens_defined) / 100) * 7;
    while (sum_symbols < symbols_limit)
      sum_symbols += token_count[i1++];
    main_max_token = i1 - 1;
    lcp_thread_data[0].min_token = i1;
    symbols_limit = ((num_in_tokens - num_tokens_defined) / 100) * 15;
    while (sum_symbols < symbols_limit)
      sum_symbols += token_count[i1++];
    lcp_thread_data[0].max_token = i1 - 1;
    lcp_thread_data[1].min_token = i1;
    symbols_limit = ((num_in_tokens - num_tokens_defined) / 100) * 23;
    while (sum_symbols < symbols_limit)
      sum_symbols += token_count[i1++];
    lcp_thread_data[1].max_token = i1 - 1;
    lcp_thread_data[2].min_token = i1;
    symbols_limit = ((num_in_tokens - num_tokens_defined) / 100) * 32;
    while (sum_symbols < symbols_limit)
      sum_symbols += token_count[i1++];
    lcp_thread_data[2].max_token = i1 - 1;
    lcp_thread_data[3].min_token = i1;
    symbols_limit = ((num_in_tokens - num_tokens_defined) / 100) * 42;
    while (sum_symbols < symbols_limit)
      sum_symbols += token_count[i1++];
    lcp_thread_data[3].max_token = i1 - 1;
    lcp_thread_data[4].min_token = i1;
    symbols_limit = ((num_in_tokens - num_tokens_defined) / 100) * 53;
    while (sum_symbols < symbols_limit)
      sum_symbols += token_count[i1++];
    lcp_thread_data[4].max_token = i1 - 1;
    lcp_thread_data[5].min_token = i1;
    symbols_limit = ((num_in_tokens - num_tokens_defined) / 100) * 65;
    while (sum_symbols < symbols_limit)
      sum_symbols += token_count[i1++];
    lcp_thread_data[5].max_token = i1 - 1;
    lcp_thread_data[6].min_token = i1;
    symbols_limit = ((num_in_tokens - num_tokens_defined) / 100) * 69;
    while (sum_symbols < symbols_limit)
      sum_symbols += token_count[i1++];
    lcp_thread_data[6].max_token = i1 - 1;
    lcp_thread_data[7].min_token = i1;
    symbols_limit = ((num_in_tokens - num_tokens_defined) / 100) * 76;
    while (sum_symbols < symbols_limit)
      sum_symbols += token_count[i1++];
    lcp_thread_data[7].max_token = i1 - 1;
    lcp_thread_data[8].min_token = i1;
    symbols_limit = ((num_in_tokens - num_tokens_defined) / 100) * 83;
    while (sum_symbols < symbols_limit)
      sum_symbols += token_count[i1++];
    lcp_thread_data[8].max_token = i1 - 1;
    lcp_thread_data[9].min_token = i1;
    symbols_limit = ((num_in_tokens - num_tokens_defined) / 100) * 89;
    while (sum_symbols < symbols_limit)
      sum_symbols += token_count[i1++];
    lcp_thread_data[9].max_token = i1 - 1;
    lcp_thread_data[10].min_token = i1;
    symbols_limit = ((num_in_tokens - num_tokens_defined) / 100) * 95;
    while (sum_symbols < symbols_limit)
      sum_symbols += token_count[i1++];
    lcp_thread_data[10].max_token = i1 - 1;
    lcp_thread_data[11].min_token = i1;
    lcp_thread_data[11].max_token = num_start_tokens - 1;

    min_token_ptr = in_token_ptr;
    stop_token_ptr = in_token_ptr;
    max_token_ptr = 0;

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
      this_token = *in_token_ptr++;
      while ((int)this_token >= 0) {
        if (this_token <= main_max_token) {
          add_suffix(this_token,in_token_ptr,&next_string_node_num);
          stop_token_ptr = in_token_ptr;
          if (next_string_node_num < main_string_nodes_limit)
            this_token = *in_token_ptr++;
          else
            goto done_building_lcp_tree;
        }
        else
          this_token = *in_token_ptr++;
      }
      if (this_token == 0xFFFFFFFE) {
        in_token_ptr--;
        break; // exit loop on EOF
      }
    }
done_building_lcp_tree:
    stop_token_ptr = in_token_ptr;
    max_token_ptr = in_token_ptr;

    unsigned int * base_node_child_num_ptr = base_string_nodes_child_node_num;
    node_ptrs_num = 0;
    if (UTF8_compliant)
      pthread_create(&rank_scores_thread1,NULL,rank_scores_thread_UTF8_compliant,(void *)&rank_scores_buffer[0]);
    else
      pthread_create(&rank_scores_thread1,NULL,rank_scores_thread,(void *)&rank_scores_buffer[0]);

    i1 = 0;
    score_nodes(main_max_token);
    while (rank_scores_buffer[node_ptrs_num - 1].node_ptrs != 0);

    pthread_join(build_lcp_thread1,NULL);
    pthread_create(&build_lcp_thread1,NULL,build_lcp_thread,(char *)&lcp_thread_data[6]);
    score_nodes(lcp_thread_data[0].max_token);
    while (rank_scores_buffer[node_ptrs_num - 1].node_ptrs != 0);

    pthread_join(build_lcp_thread2,NULL);
    pthread_create(&build_lcp_thread2,NULL,build_lcp_thread,(char *)&lcp_thread_data[7]);
    score_nodes(lcp_thread_data[1].max_token);
    while (rank_scores_buffer[node_ptrs_num - 1].node_ptrs != 0);

    pthread_join(build_lcp_thread3,NULL);
    pthread_create(&build_lcp_thread3,NULL,build_lcp_thread,(char *)&lcp_thread_data[8]);
    score_nodes(lcp_thread_data[2].max_token);
    while (rank_scores_buffer[node_ptrs_num - 1].node_ptrs != 0);

    pthread_join(build_lcp_thread4,NULL);
    pthread_create(&build_lcp_thread4,NULL,build_lcp_thread,(char *)&lcp_thread_data[9]);
    score_nodes(lcp_thread_data[3].max_token);
    while (rank_scores_buffer[node_ptrs_num - 1].node_ptrs != 0);

    pthread_join(build_lcp_thread5,NULL);
    pthread_create(&build_lcp_thread5,NULL,build_lcp_thread,(char *)&lcp_thread_data[10]);
    score_nodes(lcp_thread_data[4].max_token);
    while (rank_scores_buffer[node_ptrs_num - 1].node_ptrs != 0);

    pthread_join(build_lcp_thread6,NULL);
    pthread_create(&build_lcp_thread6,NULL,build_lcp_thread,(char *)&lcp_thread_data[11]);
    score_nodes(lcp_thread_data[5].max_token);

    pthread_join(build_lcp_thread1,NULL);
    score_nodes(lcp_thread_data[6].max_token);

    pthread_join(build_lcp_thread2,NULL);
    score_nodes(lcp_thread_data[7].max_token);

    pthread_join(build_lcp_thread3,NULL);
    score_nodes(lcp_thread_data[8].max_token);

    pthread_join(build_lcp_thread4,NULL);
    score_nodes(lcp_thread_data[9].max_token);

    pthread_join(build_lcp_thread5,NULL);
    score_nodes(lcp_thread_data[10].max_token);

    pthread_join(build_lcp_thread6,NULL);
    score_nodes(lcp_thread_data[11].max_token);
    while (rank_scores_buffer[node_ptrs_num - 1].node_ptrs != 0);

    rank_scores_buffer[node_ptrs_num].node_ptrs = 1;
    pthread_join(rank_scores_thread1,NULL);

    fprintf(stderr,"Read %u of %u symbols, start %.4f\n",
        in_token_ptr-start_token_ptr-(unsigned int)(prior_cycle_start_ratio*(float)(end_token_ptr-start_token_ptr)),
        end_token_ptr-start_token_ptr,prior_cycle_start_ratio);
    prior_cycle_end_ratio = (float)(in_token_ptr-start_token_ptr)/(end_token_ptr-start_token_ptr);

    if (num_node_scores) {
      fprintf(stderr,"Common prefix scan 0 - %x, score[%hu] = %.2f\n",
          num_start_tokens-1,num_node_scores,node_scores[node_scores_index[num_node_scores-1]].score);

      free_RAM_ptr = (unsigned char *)(end_token_ptr + 1);
      match_nodes = (struct match_node *)free_RAM_ptr;
      match_nodes[0].num_tokens = 0;
      match_nodes[0].child_ptr = 0;

      // build a prefix tree of the match strings
      num_match_nodes = 1;
      i1 = 0;
      while (i1 < num_node_scores) {
        unsigned int *best_score_match_ptr;
        best_score_match_ptr = init_best_score_ptrs();
        match_node_ptr = match_nodes;
        while (best_score_match_ptr <= best_score_last_match_ptr) {
          this_token = *best_score_match_ptr;
          if (match_node_ptr->child_ptr == 0) {
            make_and_move_to_match_child();
          }
          else {
            unsigned char sibling_number;
            move_to_match_child(match_node_ptr,sibling_number);
            if (this_token == match_node_ptr->token) {
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
        unsigned int *best_score_match_ptr;
        best_score_match_ptr = init_best_score_ptrs();
        // read the first token
        this_token = *best_score_match_ptr++;
        match_node_ptr = &match_nodes[1];
        move_to_existing_match_sibling();
        while (best_score_match_ptr <= best_score_last_match_ptr) {
          // starting with the second token, look for suffixes that are in the prefix tree
          search_match_ptr = best_score_match_ptr;
          num_tokens_in_string = 0;
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
            this_token = *search_match_ptr;
            move_to_search_sibling();
            if (this_token != search_node_ptr->token) // no child match so exit suffix search
              break;
            match_node_ptr->miss_ptr = search_node_ptr;
            search_match_ptr++;
          }
          this_token = *best_score_match_ptr++;
        }
        i1++;
      }

      // Redo the tree build and miss values with just the valid score tokens
      match_node_ptr = match_nodes + num_start_tokens;
      while (match_node_ptr-- != match_nodes)
        match_node_ptr->num_tokens = 0;
      num_match_nodes = num_start_tokens;

      i1 = 0;
      while (i1 < num_node_scores) {
        if (node_scores_bad[i1] == 0) {
          unsigned int *best_score_match_ptr;
          best_score_match_ptr = init_best_score_ptrs();
          this_token = *best_score_match_ptr++;
          match_node_ptr = &match_nodes[this_token];
          best_score_num_tokens = 1;
          if (match_node_ptr->num_tokens == 0)
            init_level_1_match_node(this_token,i1);
          while (best_score_match_ptr <= best_score_last_match_ptr) {
            this_token = *best_score_match_ptr++;
            best_score_num_tokens++;
            move_to_match_child_with_make();
          }
        }
        i1++;
      }

      // span nodes entering the longest (first) suffix match for each node
      i1 = 0;
      while (i1 < num_node_scores) {
        if (node_scores_bad[i1] == 0) {
          unsigned int *best_score_suffix_ptr;
          best_score_suffix_ptr = init_best_score_ptrs();
          suffix_node_number = *best_score_suffix_ptr++;
          // starting at the node of the 2nd token in string, match strings with prefix tree until no match found,
          //   for each match node found, if suffix miss token is zero, set it to the tree token node
          while (best_score_suffix_ptr <= best_score_last_match_ptr) {
            // follow the suffix until the end (or break on no tree matches)
            this_token = *best_score_suffix_ptr++;
            suffix_node_number = match_nodes[suffix_node_number].child_ptr - match_nodes;
            unsigned int shifted_token = this_token;
            while (this_token != match_nodes[suffix_node_number].token) {
              suffix_node_number = match_nodes[suffix_node_number].sibling_node_num[shifted_token & 0xF];
              shifted_token = shifted_token >> 4;
            }
            match_node_ptr = &match_nodes[suffix_node_number];
            unsigned int *best_score_match_ptr;
            best_score_match_ptr = best_score_suffix_ptr;

            if (match_nodes[this_token].num_tokens != 0) {
              search_node_ptr = &match_nodes[this_token];
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
                this_token = *best_score_match_ptr++;
                move_to_existing_match_child();
                move_to_search_child();
                if (this_token != search_node_ptr->token) // no matching sibling, so done with this suffix
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

      unsigned int prior_match_score_number[MAX_PRIOR_MATCHES];
      unsigned int *prior_match_end_ptr[MAX_PRIOR_MATCHES]; 
      unsigned int num_prior_matches = 0;
      in_token_ptr = start_token_ptr;
      size_t block_size = (end_token_ptr - start_token_ptr) / 8;
      unsigned int * block_ptr = start_token_ptr + block_size;
      stop_token_ptr = block_ptr + MAX_STRING_LENGTH;

      if (stop_token_ptr > end_token_ptr)
        stop_token_ptr = end_token_ptr;
      overlap_check_data[0].start_token_ptr = block_ptr;
      block_ptr += block_size;
      overlap_check_data[0].stop_token_ptr = block_ptr + MAX_STRING_LENGTH;
      overlap_check_data[1].start_token_ptr = block_ptr;
      block_ptr += block_size;
      overlap_check_data[1].stop_token_ptr = block_ptr + MAX_STRING_LENGTH;
      overlap_check_data[2].start_token_ptr = block_ptr;
      block_ptr += block_size;
      overlap_check_data[2].stop_token_ptr = block_ptr + MAX_STRING_LENGTH;
      overlap_check_data[3].start_token_ptr = block_ptr;
      block_ptr += block_size;
      overlap_check_data[3].stop_token_ptr = block_ptr + MAX_STRING_LENGTH;
      overlap_check_data[4].start_token_ptr = block_ptr;
      block_ptr += block_size;
      overlap_check_data[4].stop_token_ptr = block_ptr + MAX_STRING_LENGTH;
      overlap_check_data[5].start_token_ptr = block_ptr;
      block_ptr += block_size;
      overlap_check_data[5].stop_token_ptr = block_ptr + MAX_STRING_LENGTH;
      overlap_check_data[6].start_token_ptr = block_ptr;
      overlap_check_data[6].stop_token_ptr = end_token_ptr;
      i1 = 5;
      while (overlap_check_data[i1].stop_token_ptr > end_token_ptr) {
        overlap_check_data[i1].stop_token_ptr = end_token_ptr;
        if (i1-- == 0)
          break;
      }

      for (i1 = 0 ; i1 < 7 ; i1++)
        pthread_create(&overlap_check_threads[i1],NULL,overlap_check_thread,(char *)&overlap_check_data[i1]);

main_overlap_check_loop_no_match:
      if (in_token_ptr == stop_token_ptr)
        goto main_overlap_check_loop_end;
      this_token = *in_token_ptr++;
      if ((int)this_token < 0)
        goto main_overlap_check_loop_no_match;
      if (match_nodes[this_token].num_tokens == 0)
        goto main_overlap_check_loop_no_match;
      match_node_ptr = &match_nodes[this_token];

main_overlap_check_loop_match:
      if (in_token_ptr == stop_token_ptr)
        goto main_overlap_check_loop_end;
      this_token = *in_token_ptr++;
      if ((int)this_token < 0)
        goto main_overlap_check_loop_no_match;

      match_node_ptr = match_node_ptr->child_ptr;
      if (this_token != match_node_ptr->token) {
        unsigned int shifted_token = this_token;
        do {
          if (match_node_ptr->sibling_node_num[shifted_token & 0xF] != 0) {
            match_node_ptr = &match_nodes[match_node_ptr->sibling_node_num[shifted_token & 0xF]];
            shifted_token = shifted_token >> 4;
          }
          else {
            if (match_node_ptr->miss_ptr == 0) {
              if (match_nodes[this_token].num_tokens == 0)
                goto main_overlap_check_loop_no_match;
              match_node_ptr = &match_nodes[this_token];
              goto main_overlap_check_loop_match;
            }
            else {
              match_node_ptr = match_node_ptr->miss_ptr;
              shifted_token = this_token;
            }
          }
        } while (this_token != match_node_ptr->token);
      }
      if (match_node_ptr->child_ptr)
        goto main_overlap_check_loop_match;

      // no child, so found a match - check for overlaps
      unsigned char found_same_score_prior_match = 0;
      node_score_number = match_node_ptr->score_number;
      unsigned int prior_match_number = 0;
      while (prior_match_number < num_prior_matches) {
        if (in_token_ptr - node_scores[node_scores_index[node_score_number]].num_tokens
            > prior_match_end_ptr[prior_match_number]) {
          num_prior_matches--;
          for (i2 = prior_match_number ; i2 < num_prior_matches ; i2++) {
            prior_match_end_ptr[i2] = prior_match_end_ptr[i2+1];
            prior_match_score_number[i2] = prior_match_score_number[i2+1];
          }
        }
        else { // overlapping token substitution strings, so invalidate the lower score
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
        prior_match_end_ptr[num_prior_matches] = in_token_ptr - 1;
        prior_match_score_number[num_prior_matches++] = node_score_number;
      }
      if (match_node_ptr == 0)
        goto main_overlap_check_loop_no_match;
      else
        goto main_overlap_check_loop_match;

main_overlap_check_loop_end:
      for (i1 = 0 ; i1 < 7 ; i1++)
        pthread_join(overlap_check_threads[i1],NULL);

      // Redo the tree build and miss values with the final valid score tokens
      match_node_ptr = match_nodes + num_start_tokens;
      while (match_node_ptr-- != match_nodes)
        match_node_ptr->num_tokens = 0;

      num_match_nodes = num_start_tokens;
      max_string_length = 0;
      i2 = num_tokens_defined;
      i1 = 0;
      while (i1 < num_node_scores) {
        if (node_scores_bad[i1] == 0) {
          unsigned int *best_score_match_ptr;
          best_score_match_ptr = init_best_score_ptrs();
          this_token = *best_score_match_ptr++;
          best_score_num_tokens = 1;
          match_node_ptr = &match_nodes[this_token];
          if (match_node_ptr->num_tokens == 0)
            init_level_1_match_node(this_token,i1);
          while (best_score_match_ptr <= best_score_last_match_ptr) {
            this_token = *best_score_match_ptr++;
            best_score_num_tokens++;
            move_to_match_child_with_make();
          }
          if (best_score_num_tokens > max_string_length)
            max_string_length = best_score_num_tokens;
          token_count[num_base_tokens+i2] = 0;
          new_token_number[i1] = i2++;
        }
        i1++;
      }
      max_string_length += 3;

      match_strings = (unsigned int *)((size_t)free_RAM_ptr + (size_t)num_match_nodes * sizeof(struct match_node));

      // span nodes entering the longest (first) suffix match for each node
      i1 = 0;
      while (i1 < num_node_scores) {
        if (node_scores_bad[i1] == 0) {
          unsigned int *best_score_suffix_ptr;
          best_score_suffix_ptr = init_best_score_ptrs();
          suffix_node_number = *best_score_suffix_ptr++;
          // starting at the node of the 2nd token in string, match strings with prefix tree until no match found,
          //   for each match node found, if suffix miss token is zero, set it to the tree token node
          while (best_score_suffix_ptr <= best_score_last_match_ptr) {
            // follow the suffix until the end (or break on no tree matches)
            this_token = *best_score_suffix_ptr++;
            suffix_node_number = match_nodes[suffix_node_number].child_ptr - match_nodes;
            unsigned int shifted_token = this_token;
            while (this_token != match_nodes[suffix_node_number].token) {
              suffix_node_number = match_nodes[suffix_node_number].sibling_node_num[shifted_token & 0xF];
              shifted_token = shifted_token >> 4;
            }
            match_node_ptr = &match_nodes[suffix_node_number];
            unsigned int *best_score_match_ptr;
            best_score_match_ptr = best_score_suffix_ptr;

            if (match_nodes[this_token].num_tokens != 0) {
              search_node_ptr = &match_nodes[this_token];
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
                this_token = *best_score_match_ptr++;
                move_to_existing_match_child();
                move_to_search_child();
                if (this_token != search_node_ptr->token) // no matching sibling, so done with this suffix
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
        // save the match strings so they can be added to the end of the data after token substitution is done
        match_string_start_ptr = &match_strings[(unsigned int)i1 * max_string_length];
        node_string_start_ptr = start_token_ptr + node_scores[node_scores_index[i1]].last_match_index1
          - node_scores[node_scores_index[i1]].num_tokens + 1;
        for (i2 = 0 ; i2 < node_scores[node_scores_index[i1]].num_tokens ; i2++)
          *(match_string_start_ptr + i2) = *(node_string_start_ptr + i2);
        i1++;
      }

      fprintf(stderr,"Replacing data with new dictionary symbols\r");
      // scan the data following the prefix tree and substitute new tokens on end matches (child is 0)
      stop_token_ptr = start_token_ptr + ((end_token_ptr - start_token_ptr) >> 3);
      find_substitutions_data[0].start_token_ptr = stop_token_ptr;
      block_size = (end_token_ptr - start_token_ptr) / 7;
      block_ptr = stop_token_ptr + block_size;
      find_substitutions_data[0].stop_token_ptr = block_ptr;
      find_substitutions_data[1].start_token_ptr = block_ptr;
      block_ptr += block_size;
      find_substitutions_data[1].stop_token_ptr = block_ptr;
      find_substitutions_data[2].start_token_ptr = block_ptr;
      block_ptr += block_size;
      find_substitutions_data[2].stop_token_ptr = block_ptr;
      find_substitutions_data[3].start_token_ptr = block_ptr;
      block_ptr += block_size;
      find_substitutions_data[3].stop_token_ptr = block_ptr;
      find_substitutions_data[4].start_token_ptr = block_ptr;
      block_ptr += block_size;
      find_substitutions_data[4].stop_token_ptr = block_ptr;
      find_substitutions_data[5].start_token_ptr = block_ptr;
      find_substitutions_data[5].stop_token_ptr = end_token_ptr;

      for (i1 = 0 ; i1 < 6 ; i1++) {
        find_substitutions_data[i1].done = 0;
        find_substitutions_data[i1].num_substitutions = 0;
        pthread_create(&find_substitutions_threads[i1],NULL,find_substitutions_thread,(char *)&find_substitutions_data[i1]);
      }

      unsigned int extra_match_symbols = 0;
      unsigned short int substitute_index = 0;
      num_tokens_to_copy = 0;
      in_token_ptr = start_token_ptr;
      out_token_ptr = start_token_ptr;

      pthread_create(&substitute_thread1,NULL,substitute_thread,NULL);
      if (in_token_ptr == stop_token_ptr)
        goto main_token_substitution_loop_end;
      this_token = *in_token_ptr++;
      if ((int)this_token >= 0) {
main_token_substitution_loop_no_match_with_symbol:
        match_node_ptr = &match_nodes[this_token];
        if (match_node_ptr->num_tokens) {
          this_token = *in_token_ptr++;
          if ((int)this_token >= 0) {
            if (match_node_ptr->child_ptr == 0) {
              if (num_tokens_to_copy >= 100000) {
                if ((substitute_index & 0x7FFF) == 0x7FFF);
                  while (substitute_data[substitute_index & 0x8000]);
                substitute_data[substitute_index++] = num_tokens_to_copy;
                num_tokens_to_copy = 0;
              }
              if (in_token_ptr == stop_token_ptr)
                goto main_token_substitution_loop_end;
              this_token = *in_token_ptr++;
              if ((int)this_token >= 0)
                goto main_token_substitution_loop_no_match_with_symbol;
              num_tokens_to_copy++;
              if (in_token_ptr == stop_token_ptr)
                goto main_token_substitution_loop_end;
              this_token = *in_token_ptr++;
              goto main_token_substitution_loop_no_match_with_symbol;
            }
main_token_substitution_loop_match_with_child:
            match_node_ptr = match_node_ptr->child_ptr;
            if (this_token != match_node_ptr->token) {
              unsigned int sibling_nibble = this_token;
              do {
                if (match_node_ptr->sibling_node_num[sibling_nibble & 0xF]) {
                  match_node_ptr = &match_nodes[match_node_ptr->sibling_node_num[sibling_nibble & 0xF]];
                  sibling_nibble = sibling_nibble >> 4;
                }
                else { // no match, so use miss node and output missed tokens
                  if (match_node_ptr->miss_ptr == 0) {
                    if (match_nodes[this_token].num_tokens) {
                      if (in_token_ptr > stop_token_ptr) {
                        num_tokens_to_copy += match_node_ptr->num_tokens - (in_token_ptr - stop_token_ptr);
                        goto main_token_substitution_loop_end;
                      }
                      sibling_nibble = sibling_nibble >> 4;
                      num_tokens_to_copy += match_node_ptr->num_tokens - 1;
                      match_node_ptr = &match_nodes[this_token];
                    }
                    else {
                      if (in_token_ptr >= stop_token_ptr) {
                        num_tokens_to_copy += match_node_ptr->num_tokens - (in_token_ptr - stop_token_ptr);
                        goto main_token_substitution_loop_end;
                      }
                      num_tokens_to_copy += match_node_ptr->num_tokens;
                      if (num_tokens_to_copy >= 100000) {
                        if ((substitute_index & 0x7FFF) == 0x7FFF);
                          while (substitute_data[substitute_index & 0x8000]);
                        substitute_data[substitute_index++] = num_tokens_to_copy;
                        num_tokens_to_copy = 0;
                      }
                      if (in_token_ptr == stop_token_ptr)
                        goto main_token_substitution_loop_end;
                      this_token = *in_token_ptr++;
                      if ((int)this_token >= 0)
                        goto main_token_substitution_loop_no_match_with_symbol;
                      num_tokens_to_copy++;
                      if (in_token_ptr == stop_token_ptr)
                        goto main_token_substitution_loop_end;
                      this_token = *in_token_ptr++;
                      goto main_token_substitution_loop_no_match_with_symbol;
                    }
                  }
                  else {
                    num_tokens_to_copy += match_node_ptr->num_tokens - match_node_ptr->miss_ptr->num_tokens;
                    if (in_token_ptr - match_node_ptr->miss_ptr->num_tokens >= stop_token_ptr) {
                      num_tokens_to_copy -= in_token_ptr - stop_token_ptr - match_node_ptr->miss_ptr->num_tokens;
                      goto main_token_substitution_loop_end;
                    }
                    match_node_ptr = match_node_ptr->miss_ptr;
                    sibling_nibble = this_token;
                  }
                }
              } while (this_token != match_node_ptr->token);
            }
            if (match_node_ptr->child_ptr == 0) { // no child, so found a match
              if (num_tokens_to_copy) {
                if ((substitute_index & 0x7FFF) == 0x7FFF);
                  while (substitute_data[substitute_index & 0x8000]);
                substitute_data[substitute_index++] = num_tokens_to_copy;
                num_tokens_to_copy = 0;
              }
              node_score_number = match_node_ptr->score_number;
              if ((substitute_index & 0x7FFF) == 0x7FFF);
                while (substitute_data[substitute_index & 0x8000]);
              substitute_data[substitute_index++] = 0x80000000 + match_node_ptr->num_tokens;
              if ((substitute_index & 0x7FFF) == 0x7FFF);
                while (substitute_data[substitute_index & 0x8000]);
              substitute_data[substitute_index++] = num_base_tokens + new_token_number[node_score_number];
              if (in_token_ptr >= stop_token_ptr) {
                extra_match_symbols = in_token_ptr - stop_token_ptr;
                goto main_token_substitution_loop_end;
              }
              this_token = *in_token_ptr++;
              if ((int)this_token >= 0)
                goto main_token_substitution_loop_no_match_with_symbol;
              num_tokens_to_copy++;
              if (in_token_ptr == stop_token_ptr)
                goto main_token_substitution_loop_end;
              this_token = *in_token_ptr++;
              goto main_token_substitution_loop_no_match_with_symbol;
            }
            if (num_tokens_to_copy >= 100000) {
              if ((substitute_index & 0x7FFF) == 0x7FFF);
                while (substitute_data[substitute_index & 0x8000]);
              substitute_data[substitute_index++] = num_tokens_to_copy;
              num_tokens_to_copy = 0;
            }
            this_token = *in_token_ptr++;
            if ((int)this_token >= 0)
              goto main_token_substitution_loop_match_with_child;
            num_tokens_to_copy += match_node_ptr->num_tokens + 1;
            if (in_token_ptr >= stop_token_ptr) {
              num_tokens_to_copy -= in_token_ptr - stop_token_ptr;
              goto main_token_substitution_loop_end;
            }
            this_token = *in_token_ptr++;
            goto main_token_substitution_loop_no_match_with_symbol;
          }
          else { // define token
            num_tokens_to_copy += match_node_ptr->num_tokens + 1;
            if (in_token_ptr >= stop_token_ptr) {
              num_tokens_to_copy -= in_token_ptr - stop_token_ptr;
              goto main_token_substitution_loop_end;
            }
            this_token = *in_token_ptr++;
            goto main_token_substitution_loop_no_match_with_symbol;
          }
        }
        if (++num_tokens_to_copy <= 100000) {
          if (in_token_ptr == stop_token_ptr)
            goto main_token_substitution_loop_end;
          this_token = *in_token_ptr++;
          if ((int)this_token >= 0)
            goto main_token_substitution_loop_no_match_with_symbol;
          num_tokens_to_copy++;
          if (in_token_ptr == stop_token_ptr)
            goto main_token_substitution_loop_end;
          this_token = *in_token_ptr++;
          goto main_token_substitution_loop_no_match_with_symbol;
        }
        if ((substitute_index & 0x7FFF) == 0x7FFF);
          while (substitute_data[substitute_index & 0x8000]);
        substitute_data[substitute_index++] = num_tokens_to_copy;
        num_tokens_to_copy = 0;
        if (in_token_ptr == stop_token_ptr)
          goto main_token_substitution_loop_end;
        this_token = *in_token_ptr++;
        if ((int)this_token >= 0)
          goto main_token_substitution_loop_no_match_with_symbol;
        num_tokens_to_copy = 1;
        if (in_token_ptr == stop_token_ptr)
          goto main_token_substitution_loop_end;
        this_token = *in_token_ptr++;
        goto main_token_substitution_loop_no_match_with_symbol;
      }
      else { // define token
        num_tokens_to_copy++;
        if (in_token_ptr == stop_token_ptr)
          goto main_token_substitution_loop_end;
        this_token = *in_token_ptr++;
        goto main_token_substitution_loop_no_match_with_symbol;
      }

main_token_substitution_loop_end:
      if (num_tokens_to_copy) {
        if ((substitute_index & 0x7FFF) == 0x7FFF);
          while (substitute_data[substitute_index & 0x8000]);
        substitute_data[substitute_index++] = num_tokens_to_copy;
      }

      for (i1 = 0 ; i1 < 6 ; i1++) {
        unsigned int num_substitutions;
        unsigned int i2 = 0;
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
                find_substitutions_data[i1].data[1] = find_substitutions_data[i1].data[0]
                    + find_substitutions_data[i1].data[1] - extra_match_symbols;
                extra_match_symbols -= find_substitutions_data[i1].data[0];
                if (num_substitutions == 1)
                  i2 = 1;
                else {
                  i2 = 2;
                  find_substitutions_data[i1].data[2] = find_substitutions_data[i1].data[1] - 0x80000000 - extra_match_symbols;
                  extra_match_symbols = 0;
                }
              }
            }
            else {
              find_substitutions_data[i1].data[1] = find_substitutions_data[i1].data[0] - 0x80000000 - extra_match_symbols;
              i2 = 1;
              extra_match_symbols = 0;
            }
          }
          while (i2 != num_substitutions) { // send find_substitutions thread data
            if ((substitute_index & 0x7FFF) == 0x7FFF);
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
              find_substitutions_data[i1].data[1] = find_substitutions_data[i1].data[0]
                  + find_substitutions_data[i1].data[1] - extra_match_symbols;
              extra_match_symbols -= find_substitutions_data[i1].data[0];
              if (num_substitutions == 1)
                i2 = 1;
              else {
                i2 = 2;
                find_substitutions_data[i1].data[2] = find_substitutions_data[i1].data[1] - 0x80000000 - extra_match_symbols;
                extra_match_symbols = 0;
              }
            }
          }
          else {
            find_substitutions_data[i1].data[1] = find_substitutions_data[i1].data[0] - 0x80000000 - extra_match_symbols;
            i2 = 1;
            extra_match_symbols = 0;
          }
        }
        while (i2 != num_substitutions) { // send find_substitutions thread data
          if ((substitute_index & 0x7FFF) == 0x7FFF);
            while (substitute_data[substitute_index & 0x8000]);
          substitute_data[substitute_index++] = find_substitutions_data[i1].data[i2 & 0x3FFFFF];
          find_substitutions_data[i1].data[i2 & 0x3FFFFF] = 0;
          i2++;
        }
        extra_match_symbols += find_substitutions_data[i1].extra_match_symbols;
      }

      if ((substitute_index & 0x7FFF) == 0x7FFF);
        while (substitute_data[substitute_index]);
      substitute_data[substitute_index] = 0xFFFFFFFF;
      pthread_join(substitute_thread1,NULL);

      // Add the new token definitions to the end of the data
      i1 = 0;
      while (i1 < num_node_scores) {
        if (node_scores_bad[i1] == 0) {
          unsigned int *match_string_ptr, *match_string_end_ptr;
          *out_token_ptr++ = first_token_number + num_tokens_defined++;
          match_string_ptr = match_strings + max_string_length * (unsigned int)i1;
          match_string_end_ptr = match_string_ptr + node_scores[node_scores_index[i1++]].num_tokens;
          while (match_string_ptr != match_string_end_ptr) {
            token_count[*match_string_ptr] -= token_count[num_base_tokens+num_tokens_defined-1] - 1;
            *out_token_ptr++ = *match_string_ptr++;
          }
        }
        else
          node_scores_bad[i1++] = 0;
      }
      end_token_ptr = out_token_ptr;
      *end_token_ptr = 0xFFFFFFFE;
      free_RAM_ptr = (unsigned char *)(end_token_ptr + 1);
    }

    if (num_node_scores) {
      if (scan_cycle > 1) {
        if (num_node_scores == max_scores) {
          if (min_score < prior_min_score) {
            if (scan_cycle > 50) {
              if (scan_cycle > 100)
                new_min_score = 0.993 * min_score * (min_score / prior_min_score) - 0.05;
              else
                new_min_score = 0.99 * min_score * (min_score / prior_min_score) - 0.1;
            }
            else
              new_min_score = 0.98 * min_score * (min_score / prior_min_score) - 0.1;
          }
          else
            new_min_score = 0.475 * (prior_min_score + min_score);
        }
        else {
          if (min_score < prior_min_score)
            new_min_score = 0.96 * min_score * (min_score / prior_min_score) - 0.2;
          else
            new_min_score = 0.46 * (prior_min_score + min_score) - 0.2;
        }
      }
      else {
        new_min_score = (double)(0.75 * node_scores[node_scores_index[num_node_scores-1]].score);
        prior_min_score = min_score;
      }
    }

    else if (min_score > 0.5) {
      new_min_score = 0.5;
      num_node_scores = 1;
    }
    if (min_score < prior_min_score)
      prior_min_score = min_score;
    if (new_min_score < prior_min_score)
      min_score = new_min_score;
    else
      min_score = 0.98 * prior_min_score;
    if (min_score < 0.5)
      min_score = 0.5;

    max_scores = (max_scores + 2 * (((29 * (num_base_tokens + num_tokens_defined - num_start_tokens)) >> 5) + 7000)) / 3;
    if (max_scores > MAX_SCORES)
      max_scores = MAX_SCORES;

    if (num_node_scores == 0) {
write_file:
      sprintf(out_file_name,"%s",argv[arg_num]);
      if ((fd_out = fopen(out_file_name,"wb+")) == NULL) {
        fprintf(stderr,"ERROR - unable to open output file '%s'\n",out_file_name);
        exit(0);
      }

      in_char_ptr = char_buffer;
      *in_char_ptr++ = cap_encoded + (delta_gap * 2);
      in_token_ptr = start_token_ptr;
      if (UTF8_compliant) {
        while (in_token_ptr != end_token_ptr) {
          unsigned int token_value;
          token_value = *in_token_ptr++;
          if (token_value < 0x80)
            *in_char_ptr++ = (unsigned char)token_value;
          else if (token_value < 0x800) {
            *in_char_ptr++ = 0xC0 + (token_value >> 6);
            *in_char_ptr++ = 0x80 + (token_value & 0x3F);
          }
          else if (token_value < 0x10000) {
            *in_char_ptr++ = 0xE0 + (token_value >> 12);
            *in_char_ptr++ = 0x80 + ((token_value >> 6) & 0x3F);
            *in_char_ptr++ = 0x80 + (token_value & 0x3F);
          }
          else if (token_value < START_MY_TOKENS) {
            *in_char_ptr++ = 0xF0 + (token_value >> 18);
            *in_char_ptr++ = 0x80 + ((token_value >> 12) & 0x3F);
            *in_char_ptr++ = 0x80 + ((token_value >> 6) & 0x3F);
            *in_char_ptr++ = 0x80 + (token_value & 0x3F);
          }
          else if ((int)token_value >= 0) {
            token_value -= START_MY_TOKENS;
            *in_char_ptr++ = INSERT_TOKEN_CHAR;
            *in_char_ptr++ = (unsigned char)((token_value >> 16) & 0xFF);
            *in_char_ptr++ = (unsigned char)((token_value >> 8) & 0xFF);
            *in_char_ptr++ = (unsigned char)(token_value & 0xFF);
          }
          else {
            token_value -= 0x80000000 + START_MY_TOKENS;
            *in_char_ptr++ = DEFINE_TOKEN_CHAR;
            *in_char_ptr++ = (unsigned char)((token_value >> 16) & 0xFF);
            *in_char_ptr++ = (unsigned char)((token_value >> 8) & 0xFF);
            *in_char_ptr++ = (unsigned char)(token_value & 0xFF);
          }
        }
      }
      else {
        while (in_token_ptr != end_token_ptr) {
          unsigned int token_value;
          token_value = *in_token_ptr++;
          if (token_value < INSERT_TOKEN_CHAR)
            *in_char_ptr++ = (unsigned char)token_value;
          else if (token_value == INSERT_TOKEN_CHAR) {
            *in_char_ptr++ = INSERT_TOKEN_CHAR;
            *in_char_ptr++ = DEFINE_TOKEN_CHAR;
          }
          else if (token_value == DEFINE_TOKEN_CHAR) {
            *in_char_ptr++ = DEFINE_TOKEN_CHAR;
            *in_char_ptr++ = DEFINE_TOKEN_CHAR;
          }
          else if ((int)token_value >= 0) {
            token_value -= 0x100;
            *in_char_ptr++ = INSERT_TOKEN_CHAR;
            *in_char_ptr++ = (unsigned char)((token_value >> 16) & 0xFF);
            *in_char_ptr++ = (unsigned char)((token_value >> 8) & 0xFF);
            *in_char_ptr++ = (unsigned char)(token_value & 0xFF);
          }
          else {
            token_value -= 0x80000000 + 0x100;
            *in_char_ptr++ = DEFINE_TOKEN_CHAR;
            *in_char_ptr++ = (unsigned char)((token_value >> 16) & 0xFF);
            *in_char_ptr++ = (unsigned char)((token_value >> 8) & 0xFF);
            *in_char_ptr++ = (unsigned char)(token_value & 0xFF);
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
      fclose(fd_out);
    }
  } while (num_node_scores);

  free(start_token_ptr);
  fprintf(stderr,"\nRun time %0.3f seconds.\n", (float)((unsigned long long)clock()-start_time)/1000);
}


