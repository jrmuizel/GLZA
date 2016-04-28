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

// GLZAcompressFast.c
//   Does the following:
//     1. Reads input, determines capital encoding and UTF-8 compliance.
//     2. (Optionally) builds the suffix tree for symbols starting with ASCII 0xA and deduplicates profitable repeats.
//     3. (Optionally) builds the suffix tree for symbols starting with ASCII 0x20 and deduplicates profitable repeats.
//     4. Deduplicates runs of the same symbol that have overlaps when profitable (overlap hack).
//     5. Builds the suffix tree for the data, parses left to right and creates profitable symbols and maintains the suffix tree.
//
// Usage:
//   GLZAcompressFast [-p#] [-w#] [-c#] [-m#] <infilename> <outfilename>
//       p specifies the paragraph deduplication minimum score.  Must not be negative.  Zero disables.
//       w specifies the word deduplication minimum score.  Must not be negative.  Zero disables.
//       c specifies the string deduplication minimum score.  Must not be negative.
//       m specifies the approximate RAM usage / input file size ratio (default 6.5 for UTF-8 compliant
//       files, 10.5 for non UTF-8 compliant files, minimum is 5.0).

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <pthread.h>
#include "GLZA.h"

const U32 START_MY_SYMBOLS = 0x00080000;
const U32 MAX_WRITE_SIZE = 0x200000;
const U32 BASE_NODES_CHILD_ARRAY_SIZE = 2;
const U32 BLANK = 0xFFFFFFFF;
const U32 EOF_SYMBOL = 0xFFFFFFFE;
const U32 FREE_NODES_LIST_SIZE = 0x10000;
const U16 MAX_STRING_LENGTH = 40000;
const U8 INSERT_SYMBOL_CHAR = 0xFE;
const U8 DEFINE_SYMBOL_CHAR = 0xFF;

static struct string_node {
  U32 symbol;
  U32 match_start_index;
  U32 sibling_node_num[2];
  U32 instances;
  U32 child_node_num;
  U16 num_extra_symbols;
  U8 found_overlap;
} *string_nodes, *free_node_ptr, *node_ptr;

static struct run_string_node {
  U32 symbol;
  U32 match_start_index;
  U32 sibling_node_num[2];
  U32 instances;
  U32 no_overlap_instances;
  U32 child_node_num;
  U16 num_extra_symbols;
  U8 found_overlap;
} *run_string_nodes, *run_node_ptr;

static struct back_node {
  U32 symbol;
  U32 last_match_index;
  U32 sibling_node_num[2];
  U32 instances;
  U32 child_node_num;
  U32 next_back_node_num;
  U32 depth;
} *back_nodes;

static struct match_start_node {
  U32 match_index;
  U32 depth;
  U32 child_node_num1;
  U32 child_node_num2;
} *match_start_nodes;

U32 this_symbol, num_in_symbols, new_symbol_index, match_start_index, next_string_node_num, shifted_search_symbol, i1;
U32 num_rules, num_rules_defined, num_base_symbols, num_paragraph_symbols;
U32 match_list_length, free_nodes_list_length, next_match_index_index, sorted_match_index;
U32 *symbol_ptr, *start_symbol_ptr, *end_symbol_ptr, *in_symbol_ptr, *out_symbol_ptr;
U32 *match_list, *best_score_last_match_ptr, *prior_node_num_ptr, *node_last_match_ptr;
U32 match_start_indexes[30000000];
U32 node_list[40001], first_back_node_of_depth[40001], free_nodes_list[0x10000];
U32 symbol_count[10000000], base_string_nodes_child_node_num[20000000];
U16 node_ptrs_num, best_length;
U8 found_new_rule, found_overlap;
U8 *char_buffer, *in_char_ptr, *end_char_ptr;
double production_cost, log_num_symbols, log_num_symbols_plus_tokenization_cost, best_score;
double string_score[40001];
struct string_node *first_single_instance_node_ptr, *end_match_node_ptr, *prior_node_ptr, *best_node_ptr;
struct string_node *string_node_ptr[40001];



#define write_node_ptr_data(node_ptr1, symbol1, match_start_index1, sib0, sib1, instances1, child_node_num1, extra_symbols, \
    found_overlap1) { \
  node_ptr1->symbol = symbol1; \
  node_ptr1->match_start_index = match_start_index1; \
  node_ptr1->sibling_node_num[0] = sib0; \
  node_ptr1->sibling_node_num[1] = sib1; \
  node_ptr1->instances = instances1; \
  node_ptr1->child_node_num = child_node_num1; \
  node_ptr1->num_extra_symbols = extra_symbols; \
  node_ptr1->found_overlap = found_overlap1; \
}


#define write_run_node_ptr_data(node_ptr1, symbol1, match_start_index1, sib0, sib1, instances1, no_overlap_instances1, \
    child_node_num1, extra_symbols, found_overlap1) { \
  node_ptr1->symbol = symbol1; \
  node_ptr1->match_start_index = match_start_index1; \
  node_ptr1->sibling_node_num[0] = sib0; \
  node_ptr1->sibling_node_num[1] = sib1; \
  node_ptr1->instances = instances1; \
  node_ptr1->no_overlap_instances = no_overlap_instances1; \
  node_ptr1->child_node_num = child_node_num1; \
  node_ptr1->num_extra_symbols = extra_symbols; \
  node_ptr1->found_overlap = found_overlap1; \
}


#define initialize_back_node_data(back_node_num, node_symbol, index, node_depth) { \
  back_nodes[back_node_num].symbol = node_symbol; \
  back_nodes[back_node_num].last_match_index = index; \
  back_nodes[back_node_num].sibling_node_num[0] = 0; \
  back_nodes[back_node_num].sibling_node_num[1] = 0; \
  back_nodes[back_node_num].instances = 1; \
  back_nodes[back_node_num].child_node_num = 0; \
  back_nodes[back_node_num].depth = node_depth; \
}


static inline void add_suffix(U32 * first_symbol_ptr)
{
  struct string_node *child_ptr;
  U32 match_start_index = first_symbol_ptr - start_symbol_ptr;
  U32 * in_symbol_ptr = first_symbol_ptr;
  U32 this_symbol = *in_symbol_ptr++;
  U32 search_symbol = *in_symbol_ptr;
  U16 num_extra_symbols;

  prior_node_num_ptr = &base_string_nodes_child_node_num[this_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)];
  if (*prior_node_num_ptr == 0) { // first base node child, so create a child
    *prior_node_num_ptr = next_string_node_num;
    child_ptr = &string_nodes[next_string_node_num++];
    write_node_ptr_data(child_ptr, search_symbol, match_start_index, 0, 0, 1, 0, 0, 0);
    return;
  }
  child_ptr = &string_nodes[*prior_node_num_ptr];
  if (search_symbol != child_ptr->symbol) { // follow siblings until match found or end of siblings found
    shifted_search_symbol = search_symbol;
    do {
      shifted_search_symbol >>= 1;
      prior_node_num_ptr = &child_ptr->sibling_node_num[shifted_search_symbol & 1];
      if (*prior_node_num_ptr == 0) {
        *prior_node_num_ptr = next_string_node_num;
        child_ptr = &string_nodes[next_string_node_num++];
        write_node_ptr_data(child_ptr, search_symbol, match_start_index, 0, 0, 1, 0, 0, 0);
        return;
      }
      child_ptr = &string_nodes[*prior_node_num_ptr];
    } while (search_symbol != child_ptr->symbol);
  }

  // found a matching sibling
  while (child_ptr->child_node_num) {
    // matching sibling with child so check length of match
    num_extra_symbols = child_ptr->num_extra_symbols;
    U32 * child_symbol_ptr = in_symbol_ptr - match_start_index + child_ptr->match_start_index;
    if (num_extra_symbols) {
      U16 length = 1;
      do {
        if (*(child_symbol_ptr + length) != *(in_symbol_ptr + length)) { /* insert node in branch */
          child_ptr->num_extra_symbols = length - 1;
          U32 move_child_num = child_ptr->child_node_num;
          child_ptr->child_node_num = next_string_node_num;
          node_ptr = &string_nodes[next_string_node_num++];
          U8 overlap;
          if ((first_symbol_ptr >= child_symbol_ptr + length) && (child_ptr->found_overlap == 0))
            overlap = 0;
          else
            overlap = 1;
          if ((*(in_symbol_ptr + length) & 1) == 0) {
            write_node_ptr_data(node_ptr, *(child_symbol_ptr + length), child_ptr->match_start_index, next_string_node_num, 0,
                child_ptr->instances, move_child_num, num_extra_symbols - length, overlap);
          }
          else {
            write_node_ptr_data(node_ptr, *(child_symbol_ptr + length), child_ptr->match_start_index, 0, next_string_node_num,
                child_ptr->instances, move_child_num, num_extra_symbols - length, overlap);
          }
          node_ptr = &string_nodes[next_string_node_num++];
          write_node_ptr_data(node_ptr, *(in_symbol_ptr + length), match_start_index, 0, 0, 1, 0, 0, 0);
          child_ptr->match_start_index = match_start_index;
          if (first_symbol_ptr <= child_symbol_ptr + num_extra_symbols)
            child_ptr->found_overlap = 1;
          child_ptr->instances++;
          return;
        }
      } while (length++ != num_extra_symbols);
      in_symbol_ptr += num_extra_symbols + 1;
      if (first_symbol_ptr <= child_symbol_ptr + num_extra_symbols)
        child_ptr->found_overlap = 1;
    }
    else {
      in_symbol_ptr++;
      if (first_symbol_ptr <= child_symbol_ptr)
        child_ptr->found_overlap = 1;
    }
    child_ptr->instances++;
    child_ptr->match_start_index = match_start_index;
    search_symbol = *in_symbol_ptr;
    if (in_symbol_ptr - first_symbol_ptr - 1 > MAX_STRING_LENGTH)
      search_symbol = 0xFFFFFFFF - match_start_index;
    prior_node_num_ptr = &child_ptr->child_node_num;
    child_ptr = &string_nodes[*prior_node_num_ptr];
    if (search_symbol != child_ptr->symbol) { // follow siblings until match found or end of siblings found
      shifted_search_symbol = search_symbol;
      do {
        prior_node_num_ptr = &child_ptr->sibling_node_num[shifted_search_symbol & 1];
        if (*prior_node_num_ptr == 0) {
          *prior_node_num_ptr = next_string_node_num;
          child_ptr = &string_nodes[next_string_node_num++];
          write_node_ptr_data(child_ptr, search_symbol, match_start_index, 0, 0, 1, 0, 0, 0);
          return;
        }
        child_ptr = &string_nodes[*prior_node_num_ptr];
        shifted_search_symbol >>= 1;
      } while (search_symbol != child_ptr->symbol);
    }
  }
  // matching child without grandchild so create grandchild for previous instance then add string to grandchild
  child_ptr->instances++;
  child_ptr->child_node_num = next_string_node_num;
  U16 length = 1;
  U32 * child_symbol_ptr = in_symbol_ptr - match_start_index + child_ptr->match_start_index;
  while ((*(child_symbol_ptr + length) == *(in_symbol_ptr + length))
      && (in_symbol_ptr - first_symbol_ptr - 1 < MAX_STRING_LENGTH)) {
    length++;
  }
  child_ptr->num_extra_symbols = length - 1;
  node_ptr = &string_nodes[next_string_node_num++];
  if ((*(in_symbol_ptr + length) & 1) == 0) {
    write_node_ptr_data(node_ptr, *(child_symbol_ptr + length), child_ptr->match_start_index, next_string_node_num, 0,
        1, 0, 0, 0);
  }
  else {
    write_node_ptr_data(node_ptr, *(child_symbol_ptr + length), child_ptr->match_start_index, 0, next_string_node_num,
        1, 0, 0, 0);
  }
  node_ptr = &string_nodes[next_string_node_num++];
  write_node_ptr_data(node_ptr, *(in_symbol_ptr + length), match_start_index, 0, 0, 1, 0, 0, 0);
  child_ptr->match_start_index = match_start_index;
  if (first_symbol_ptr < child_symbol_ptr + length)
    child_ptr->found_overlap = 1;
  return;
}


static inline void add_run_suffix(U32 * first_symbol_ptr)
{
  struct run_string_node *child_ptr;
  U32 match_start_index = first_symbol_ptr - start_symbol_ptr;
  U32 * in_symbol_ptr = first_symbol_ptr;
  U32 this_symbol = *in_symbol_ptr++;
  U32 search_symbol = *in_symbol_ptr;
  U16 num_extra_symbols;

  prior_node_num_ptr = &base_string_nodes_child_node_num[this_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)];
  if (*prior_node_num_ptr == 0) { // first base node child, so create a child
    *prior_node_num_ptr = next_string_node_num;
    child_ptr = &run_string_nodes[next_string_node_num++];
    write_run_node_ptr_data(child_ptr, search_symbol, match_start_index, 0, 0, 1, 1, 0, 0, 0);
    return;
  }
  child_ptr = &run_string_nodes[*prior_node_num_ptr];
  if (search_symbol != child_ptr->symbol) { // follow siblings until match found or end of siblings found
    shifted_search_symbol = search_symbol;
    do {
      shifted_search_symbol >>= 1;
      prior_node_num_ptr = &child_ptr->sibling_node_num[shifted_search_symbol & 1];
      if (*prior_node_num_ptr == 0) {
        *prior_node_num_ptr = next_string_node_num;
        child_ptr = &run_string_nodes[next_string_node_num++];
        write_run_node_ptr_data(child_ptr, search_symbol, match_start_index, 0, 0, 1, 1, 0, 0, 0);
        return;
      }
      child_ptr = &run_string_nodes[*prior_node_num_ptr];
    } while (search_symbol != child_ptr->symbol);
  }

  // found a matching sibling
  while (child_ptr->child_node_num) {
    // matching sibling with child so check length of match
    num_extra_symbols = child_ptr->num_extra_symbols;
    U32 * child_symbol_ptr = in_symbol_ptr - match_start_index + child_ptr->match_start_index;
    if (num_extra_symbols) {
      U16 length = 1;
      do {
        if (*(child_symbol_ptr + length) != *(in_symbol_ptr + length)) { /* insert node in branch */
          child_ptr->num_extra_symbols = length - 1;
          U32 move_child_num = child_ptr->child_node_num;
          child_ptr->child_node_num = next_string_node_num;
          run_node_ptr = &run_string_nodes[next_string_node_num++];
          U8 overlap;
          if ((first_symbol_ptr >= child_symbol_ptr + length) && (child_ptr->found_overlap == 0))
            overlap = 0;
          else
            overlap = 1;
          if ((*(in_symbol_ptr + length) & 1) == 0) {
            write_run_node_ptr_data(run_node_ptr, *(child_symbol_ptr + length), child_ptr->match_start_index,
                next_string_node_num, 0, child_ptr->instances, child_ptr->no_overlap_instances, move_child_num,
                num_extra_symbols - length, overlap);
          }
          else {
            write_run_node_ptr_data(run_node_ptr, *(child_symbol_ptr + length), child_ptr->match_start_index,
                0, next_string_node_num, child_ptr->instances, child_ptr->no_overlap_instances, move_child_num,
                num_extra_symbols - length, overlap);
          }
          run_node_ptr = &run_string_nodes[next_string_node_num++];
          write_run_node_ptr_data(run_node_ptr, *(in_symbol_ptr + length), match_start_index, 0, 0, 1, 1, 0, 0, 0);
          child_ptr->match_start_index = match_start_index;
          if (first_symbol_ptr <= child_symbol_ptr + num_extra_symbols)
            child_ptr->found_overlap = 1;
          else
            child_ptr->no_overlap_instances++;
          child_ptr->instances++;
          return;
        }
      } while (length++ != num_extra_symbols);
      in_symbol_ptr += num_extra_symbols + 1;
      if (first_symbol_ptr <= child_symbol_ptr + num_extra_symbols)
        child_ptr->found_overlap = 1;
      else
        child_ptr->no_overlap_instances++;
    }
    else {
      in_symbol_ptr++;
      if (first_symbol_ptr <= child_symbol_ptr)
        child_ptr->found_overlap = 1;
      else
        child_ptr->no_overlap_instances++;
    }
    child_ptr->instances++;
    child_ptr->match_start_index = match_start_index;
    search_symbol = *in_symbol_ptr;
    prior_node_num_ptr = &child_ptr->child_node_num;
    child_ptr = &run_string_nodes[*prior_node_num_ptr];
    if (search_symbol != child_ptr->symbol) { // follow siblings until match found or end of siblings found
      shifted_search_symbol = search_symbol;
      do {
        prior_node_num_ptr = &child_ptr->sibling_node_num[shifted_search_symbol & 1];
        if (*prior_node_num_ptr == 0) {
          *prior_node_num_ptr = next_string_node_num;
          child_ptr = &run_string_nodes[next_string_node_num++];
          write_run_node_ptr_data(child_ptr, search_symbol, match_start_index, 0, 0, 1, 1, 0, 0, 0);
          return;
        }
        child_ptr = &run_string_nodes[*prior_node_num_ptr];
        shifted_search_symbol >>= 1;
      } while (search_symbol != child_ptr->symbol);
    }
  }
  // matching child without grandchild so create grandchild for previous instance then add string to grandchild
  child_ptr->instances++;
  child_ptr->child_node_num = next_string_node_num;
  U16 length = 1;
  U32 * child_symbol_ptr = in_symbol_ptr - match_start_index + child_ptr->match_start_index;
  while (*(child_symbol_ptr + length) == *(in_symbol_ptr + length)) {
    length++;
  }
  child_ptr->num_extra_symbols = length - 1;
  run_node_ptr = &run_string_nodes[next_string_node_num++];
  if ((*(in_symbol_ptr + length) & 1) == 0) {
    write_run_node_ptr_data(run_node_ptr, *(child_symbol_ptr + length), child_ptr->match_start_index, next_string_node_num, 0,
        1, 1, 0, 0, 0);
  }
  else {
    write_run_node_ptr_data(run_node_ptr, *(child_symbol_ptr + length), child_ptr->match_start_index, 0, next_string_node_num,
        1, 1, 0, 0, 0);
  }
  run_node_ptr = &run_string_nodes[next_string_node_num++];
  write_run_node_ptr_data(run_node_ptr, *(in_symbol_ptr + length), match_start_index, 0, 0, 1, 1, 0, 0, 0);
  child_ptr->match_start_index = match_start_index;
  if (first_symbol_ptr < child_symbol_ptr + length)
    child_ptr->found_overlap = 1;
  else
    child_ptr->no_overlap_instances++;
  return;
}


#define find_base_node_sibling() { \
  if (search_symbol != node_ptr->symbol) { \
    shifted_search_symbol = search_symbol; \
    do { \
      shifted_search_symbol >>= 1; \
      node_ptr = &string_nodes[node_ptr->sibling_node_num[shifted_search_symbol & 1]]; \
    } while (search_symbol != node_ptr->symbol); \
  } \
}


#define find_base_node_sibling_save_prior() { \
  if (search_symbol != node_ptr->symbol) { \
    shifted_search_symbol = search_symbol; \
    do { \
      shifted_search_symbol >>= 1; \
      prior_node_num_ptr = &node_ptr->sibling_node_num[shifted_search_symbol & 1]; \
      node_ptr = &string_nodes[*prior_node_num_ptr]; \
    } while (search_symbol != node_ptr->symbol); \
  } \
}


#define find_child_node_sibling() { \
  if (search_symbol != node_ptr->symbol) { \
    prior_node_num_ptr = &node_ptr->sibling_node_num[search_symbol & 1]; \
    node_ptr = &string_nodes[*prior_node_num_ptr]; \
    if (search_symbol != node_ptr->symbol) { \
      shifted_search_symbol = search_symbol; \
      do { \
        shifted_search_symbol >>= 1; \
        prior_node_num_ptr = &node_ptr->sibling_node_num[shifted_search_symbol & 1]; \
        node_ptr = &string_nodes[*prior_node_num_ptr]; \
      } while (search_symbol != node_ptr->symbol); \
    } \
  } \
}


#define find_child_node_sibling_save_prior() { \
  if (search_symbol != node_ptr->symbol) { \
    prior_node_ptr = node_ptr; \
    prior_node_num_ptr = &node_ptr->sibling_node_num[search_symbol & 1]; \
    node_ptr = &string_nodes[*prior_node_num_ptr]; \
    if (search_symbol != node_ptr->symbol) { \
      shifted_search_symbol = search_symbol; \
      do { \
        shifted_search_symbol >>= 1; \
        prior_node_ptr = node_ptr; \
        prior_node_num_ptr = &node_ptr->sibling_node_num[shifted_search_symbol & 1]; \
        node_ptr = &string_nodes[*prior_node_num_ptr]; \
      } while (search_symbol != node_ptr->symbol); \
    } \
  } \
}


#define find_last_sibling() { \
  while (*prior_node_num_ptr) { \
    node_ptr = &string_nodes[*prior_node_num_ptr]; \
    shifted_search_symbol >>= 1; \
    prior_node_num_ptr = &node_ptr->sibling_node_num[shifted_search_symbol & 1]; \
  } \
}


void get_string_starts(U32 node_num) {
  if (string_nodes[node_num].sibling_node_num[0])
    get_string_starts(string_nodes[node_num].sibling_node_num[0]);
  if (string_nodes[node_num].sibling_node_num[1])
    get_string_starts(string_nodes[node_num].sibling_node_num[1]);
  while (string_nodes[node_num].child_node_num) {
    node_num = string_nodes[node_num].child_node_num;
    if (string_nodes[node_num].sibling_node_num[0])
      get_string_starts(string_nodes[node_num].sibling_node_num[0]);
    if (string_nodes[node_num].sibling_node_num[1])
      get_string_starts(string_nodes[node_num].sibling_node_num[1]);
  }
  match_list[match_list_length++] = string_nodes[node_num].match_start_index;
}


void get_run_string_starts(U32 node_num) {
  if (run_string_nodes[node_num].sibling_node_num[0])
    get_run_string_starts(run_string_nodes[node_num].sibling_node_num[0]);
  if (run_string_nodes[node_num].sibling_node_num[1])
    get_run_string_starts(run_string_nodes[node_num].sibling_node_num[1]);
  while (run_string_nodes[node_num].child_node_num) {
    node_num = run_string_nodes[node_num].child_node_num;
    if (run_string_nodes[node_num].sibling_node_num[0])
      get_run_string_starts(run_string_nodes[node_num].sibling_node_num[0]);
    if (run_string_nodes[node_num].sibling_node_num[1])
      get_run_string_starts(run_string_nodes[node_num].sibling_node_num[1]);
  }
  match_list[match_list_length++] = run_string_nodes[node_num].match_start_index;
}


void sort_match_indexes(U32 node_num) {
  match_start_indexes[sorted_match_index++] = match_start_nodes[node_num].match_index;
  if (match_start_nodes[node_num].child_node_num1)
    sort_match_indexes(match_start_nodes[node_num].child_node_num1);
  if (match_start_nodes[node_num].child_node_num2)
    sort_match_indexes(match_start_nodes[node_num].child_node_num2);
}


#define find_last_start_match_node() { \
  while (1) { \
    if (match_start_nodes[match_start_node_num].child_node_num2) { \
      match_start_node_num_array[depth] = match_start_node_num; \
      match_start_node_num_array_child_num[depth++] = 1; \
      match_start_node_num = match_start_nodes[match_start_node_num].child_node_num2; \
    } \
    else if (match_start_nodes[match_start_node_num].child_node_num1) { \
      match_start_node_num_array[depth] = match_start_node_num; \
      match_start_node_num_array_child_num[depth++] = 0; \
      match_start_node_num = match_start_nodes[match_start_node_num].child_node_num1; \
    } \
    else \
      break; \
  } \
} \


#define remove_node() { \
  U32 * prior_node_addr_ptr = 0; \
  U32 sibling = 0; \
  do { \
    if (free_node_ptr->sibling_node_num[sibling]) { \
      struct string_node * sibling_ptr = &string_nodes[free_node_ptr->sibling_node_num[sibling]]; \
      free_node_ptr->symbol = sibling_ptr->symbol; \
      free_node_ptr->match_start_index = sibling_ptr->match_start_index; \
      free_node_ptr->instances = sibling_ptr->instances; \
      free_node_ptr->child_node_num = sibling_ptr->child_node_num; \
      free_node_ptr->num_extra_symbols = sibling_ptr->num_extra_symbols; \
      free_node_ptr->found_overlap = sibling_ptr->found_overlap; \
      prior_node_addr_ptr = &free_node_ptr->sibling_node_num[sibling]; \
      free_node_ptr = sibling_ptr; \
      sibling = 0; \
    } \
    else { \
      sibling++; \
    } \
  } while (sibling != 2); \
  if (prior_node_addr_ptr) \
    *prior_node_addr_ptr = 0; \
}


#define get_symbol(symbol) { \
  while (*++symbol_ptr == BLANK); \
  symbol = *symbol_ptr; \
} \


#define find_end_match_node_ptr_wd(suffix_start_ptr,suffix_length) { \
  symbol_ptr = suffix_start_ptr; \
  U32 first_symbol, search_symbol; \
  first_symbol = *symbol_ptr; \
  get_symbol(search_symbol); \
  node_ptr = &string_nodes[base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)]]; \
  find_base_node_sibling(); \
  U32 search_length = suffix_length - 2; \
  node_ptr->instances -= match_list_length - 1; \
  if (node_ptr->instances == 1) \
    first_single_instance_node_ptr = node_ptr; \
  else \
    first_single_instance_node_ptr = 0; \
  num_extra_symbols = node_ptr->num_extra_symbols; \
  while (search_length--) { \
    if (num_extra_symbols == 0) { \
      node_ptr = &string_nodes[node_ptr->child_node_num]; \
      get_symbol(search_symbol); \
      find_child_node_sibling(); \
      node_ptr->instances -= match_list_length - 1; \
      if ((node_ptr->instances == 1) && (first_single_instance_node_ptr == 0)) \
        first_single_instance_node_ptr = node_ptr; \
      num_extra_symbols = node_ptr->num_extra_symbols; \
    } \
    else { \
      num_extra_symbols--; \
      while (*++symbol_ptr == BLANK); \
    } \
  } \
  end_match_node_ptr = node_ptr; \
}


#define find_end_match_node_ptr(suffix_start_ptr,suffix_length) { \
  symbol_ptr = suffix_start_ptr; \
  U32 first_symbol, search_symbol; \
  first_symbol = *symbol_ptr; \
  get_symbol(search_symbol); \
  node_ptr = &string_nodes[base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)]]; \
  find_base_node_sibling(); \
  U32 search_length = suffix_length - 2; \
  num_extra_symbols = node_ptr->num_extra_symbols; \
  while (search_length--) { \
    if (num_extra_symbols == 0) { \
      node_ptr = &string_nodes[node_ptr->child_node_num]; \
      get_symbol(search_symbol); \
      find_child_node_sibling(); \
      num_extra_symbols = node_ptr->num_extra_symbols; \
    } \
    else { \
      num_extra_symbols--; \
      while (*++symbol_ptr == BLANK); \
    } \
  } \
  end_match_node_ptr = node_ptr; \
}


#define remove_match_suffix() { \
  symbol_ptr = end_match_symbol_ptr; \
  node_ptr = end_match_node_ptr; \
  do { \
    if (num_extra_symbols) { \
      num_extra_symbols--; \
      if (symbol_ptr - start_symbol_ptr == match_start_indexes[next_match_index_index]) { \
        next_match_index_index--; \
        i = best_length - 2; \
        do { \
          while (*++symbol_ptr == BLANK); \
        } while (i--); \
      } \
      while (*++symbol_ptr == BLANK); \
    } \
    else { \
      prior_node_num_ptr = &node_ptr->child_node_num; \
      U32 search_symbol = *symbol_ptr; \
      node_ptr = &string_nodes[node_ptr->child_node_num]; \
      if (symbol_ptr - start_symbol_ptr == match_start_indexes[next_match_index_index]) { \
        next_match_index_index--; \
        search_symbol = num_rules; \
        i = best_length - 2; \
        do { \
          while (*++symbol_ptr == BLANK); \
        } while (i--); \
      } \
      while (*++symbol_ptr == BLANK); \
      find_child_node_sibling_save_prior(); \
      if ((--node_ptr->instances == 1) && (first_single_instance_node_ptr == 0)) \
        first_single_instance_node_ptr = node_ptr; \
      num_extra_symbols = node_ptr->num_extra_symbols; \
    } \
  } while (node_ptr->instances); \
  free_node_ptr = node_ptr; \
  remove_node(); \
  if (node_ptr->instances == 0) { \
    *prior_node_num_ptr = 0; \
    if (first_single_instance_node_ptr) { \
      first_single_instance_node_ptr->match_start_index = prior_node_ptr->match_start_index; \
      first_single_instance_node_ptr->child_node_num = 0; \
      first_single_instance_node_ptr->num_extra_symbols = 0; \
    } \
  } \
  else { \
    if (first_single_instance_node_ptr) { \
      first_single_instance_node_ptr->match_start_index = node_ptr->match_start_index; \
      first_single_instance_node_ptr->child_node_num = 0; \
      first_single_instance_node_ptr->num_extra_symbols = 0; \
    } \
  } \
}


#define remove_match_suffix_1(suffix_start_ptr) { \
  symbol_ptr = suffix_start_ptr; \
  U32 first_symbol = *symbol_ptr; \
  U32 search_symbol; \
  get_symbol(search_symbol); \
  if (symbol_ptr - start_symbol_ptr == match_start_indexes[next_match_index_index]) { \
    next_match_index_index--; \
    search_symbol = num_rules; \
    i = best_length - 2; \
    do { \
      while (*++symbol_ptr == BLANK); \
    } while (i--); \
  } \
  while (*++symbol_ptr == BLANK); \
  prior_node_num_ptr = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)]; \
  node_ptr = &string_nodes[*prior_node_num_ptr]; \
  find_base_node_sibling_save_prior(); \
  if (--node_ptr->instances == 0) { \
    free_node_ptr = node_ptr; \
    remove_node(); \
    if (node_ptr->instances == 0) \
      *prior_node_num_ptr = 0; \
  } \
  else { \
    if (node_ptr->instances == 1) \
      first_single_instance_node_ptr = node_ptr; \
    else \
      first_single_instance_node_ptr = 0; \
    num_extra_symbols = node_ptr->num_extra_symbols; \
    do { \
      if (num_extra_symbols == 0) { \
        prior_node_num_ptr = &node_ptr->child_node_num; \
        search_symbol = *symbol_ptr; \
        node_ptr = &string_nodes[node_ptr->child_node_num]; \
        if (symbol_ptr - start_symbol_ptr == match_start_indexes[next_match_index_index]) { \
          next_match_index_index--; \
          search_symbol = num_rules; \
          i = best_length - 2; \
          do { \
            while (*++symbol_ptr == BLANK); \
          } while (i--); \
        } \
        while (*++symbol_ptr == BLANK); \
        find_child_node_sibling_save_prior(); \
        if ((--node_ptr->instances == 1) && (first_single_instance_node_ptr == 0)) \
          first_single_instance_node_ptr = node_ptr; \
        num_extra_symbols = node_ptr->num_extra_symbols; \
      } \
      else { \
        num_extra_symbols--; \
        if (symbol_ptr - start_symbol_ptr == match_start_indexes[next_match_index_index]) { \
          next_match_index_index--; \
          i = best_length - 2; \
          do { \
            while (*++symbol_ptr == BLANK); \
          } while (i--); \
        } \
        while (*++symbol_ptr == BLANK); \
      } \
    } while (node_ptr->instances); \
    free_node_ptr = node_ptr; \
    remove_node(); \
    if (node_ptr->instances == 0) { \
      *prior_node_num_ptr = 0; \
      if (first_single_instance_node_ptr) { \
        first_single_instance_node_ptr->match_start_index = prior_node_ptr->match_start_index; \
        first_single_instance_node_ptr->child_node_num = 0; \
        first_single_instance_node_ptr->num_extra_symbols = 0; \
      } \
    } \
    else { \
      if (first_single_instance_node_ptr) { \
        first_single_instance_node_ptr->match_start_index = node_ptr->match_start_index; \
        first_single_instance_node_ptr->child_node_num = 0; \
        first_single_instance_node_ptr->num_extra_symbols = 0; \
      } \
    } \
  } \
}


#define add_match_suffix() { \
  search_symbol = 0x80000001 + num_rules; \
  prior_node_num_ptr = &end_match_node_ptr->child_node_num; \
  if (*prior_node_num_ptr) { \
    node_ptr = &string_nodes[*prior_node_num_ptr]; \
    shifted_search_symbol = search_symbol; \
    prior_node_num_ptr = &node_ptr->sibling_node_num[shifted_search_symbol & 1]; \
    find_last_sibling(); \
  } \
  *prior_node_num_ptr = free_node_ptr - string_nodes; \
  write_node_ptr_data(free_node_ptr, search_symbol, new_symbol_index + suffix_index + 1, 0, 0, 1, 0, 0, 0); \
}


#define add_match_suffix_1(suffix_start_ptr) { \
  search_symbol = 0x80000001 + num_rules; \
  symbol_ptr = suffix_start_ptr; \
  U32 first_symbol = *symbol_ptr; \
  shifted_search_symbol = search_symbol; \
  prior_node_num_ptr = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)]; \
  find_last_sibling(); \
  *prior_node_num_ptr = free_node_ptr - string_nodes; \
  write_node_ptr_data(free_node_ptr, search_symbol, new_symbol_index + best_length, 0, 0, 1, 0, 0, 0); \
}


#define score_paragraph() { \
  if (node_ptr->instances == 2) { \
    double profit_per_sub = string_entropy - log_num_symbols_plus_tokenization_cost; \
    if (profit_per_sub >= production_cost) { \
      best_length = symbols_in_string; \
      best_node_ptr = node_ptr; \
      found_new_rule = 1; \
    } \
  } \
  else { \
    double d_node_instances_m_1 = (double)(node_ptr->instances - 1); \
    double profit_per_sub = string_entropy + log2(d_node_instances_m_1) - log_num_symbols_plus_tokenization_cost; \
    if (profit_per_sub >= 0.0) { \
      if (d_node_instances_m_1 * profit_per_sub >= production_cost) { \
        best_length = symbols_in_string; \
        best_node_ptr = node_ptr; \
        found_new_rule = 1; \
      } \
    } \
  } \
}


static inline void find_paragraph(U32 *first_symbol_ptr)
{
  U32 * in_symbol_ptr = first_symbol_ptr;
  U32 first_symbol = *in_symbol_ptr;
  U32 symbols_in_string = 2;
  double string_entropy = log_num_symbols - log2((double)symbol_count[first_symbol]);

  found_new_rule = 0;
  while (*++in_symbol_ptr == BLANK);
  if ((S32)*in_symbol_ptr < 0)
    return;
  U32 search_symbol = *in_symbol_ptr;
  match_start_index = first_symbol_ptr - start_symbol_ptr;
  node_ptr = &string_nodes[base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)]];

find_sibling_p:
  find_base_node_sibling();

found_sibling_p:
  if (node_ptr->instances == 1)
    return;
  string_entropy += log_num_symbols - log2((double)symbol_count[search_symbol]);
  U16 length = node_ptr->num_extra_symbols;
  U32 * next_symbol_ptr = in_symbol_ptr;
  while (*++next_symbol_ptr == BLANK);
  while (length) {
    if ((*next_symbol_ptr == 0xa) || (*next_symbol_ptr >= num_base_symbols)) {
      score_paragraph();
      return;
    }
    length--;
    in_symbol_ptr = next_symbol_ptr;
    while (*++next_symbol_ptr == BLANK);
    string_entropy += log_num_symbols - log2((double)symbol_count[*in_symbol_ptr]);
    symbols_in_string++;
  }
  if ((*next_symbol_ptr == 0xa) || (*next_symbol_ptr >= num_base_symbols)) {  // calculate this child's score
    score_paragraph();
    return;
  }
  search_symbol = *next_symbol_ptr;
  if ((S32)search_symbol >= 0) {
    node_ptr = &string_nodes[node_ptr->child_node_num];
    symbols_in_string++;
    in_symbol_ptr = next_symbol_ptr;
    if (search_symbol == node_ptr->symbol)
      goto found_sibling_p;
    if (node_ptr->sibling_node_num[search_symbol & 1]) {
      node_ptr = &string_nodes[node_ptr->sibling_node_num[search_symbol & 1]];
      goto find_sibling_p;
    }
  }
  return;
}


#define score_word() { \
  if (node_ptr->instances == 2) { \
    double profit_per_sub = string_entropy - log_num_symbols_plus_tokenization_cost; \
    if (profit_per_sub >= production_cost) { \
      best_length = symbols_in_string; \
      best_node_ptr = node_ptr; \
      found_new_rule = 1; \
    } \
  } \
  else { \
    double d_node_instances_m_1 = (double)(node_ptr->instances - 1); \
    double profit_per_sub = string_entropy + log2(d_node_instances_m_1) - log_num_symbols_plus_tokenization_cost; \
    if (profit_per_sub >= 0.0) { \
      if (d_node_instances_m_1 * profit_per_sub >= production_cost) { \
        best_length = symbols_in_string; \
        best_node_ptr = node_ptr; \
        found_new_rule = 1; \
      } \
    } \
  } \
}


static inline void find_word(U32 *first_symbol_ptr)
{
  U32 * in_symbol_ptr = first_symbol_ptr;
  U32 first_symbol = *in_symbol_ptr;
  U32 symbols_in_string = 2;
  double string_entropy = log_num_symbols - log2((double)symbol_count[first_symbol]);

  found_new_rule = 0;
  while (*++in_symbol_ptr == BLANK);
  if ((S32)*in_symbol_ptr < 0)
    return;
  U32 search_symbol = *in_symbol_ptr;
  match_start_index = first_symbol_ptr - start_symbol_ptr;
  node_ptr = &string_nodes[base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)]];

find_sibling_w:
  find_base_node_sibling();

found_sibling_w:
  if (node_ptr->instances == 1)
    return;
  string_entropy += log_num_symbols - log2((double)symbol_count[search_symbol]);
  U16 length = node_ptr->num_extra_symbols;
  U32 * next_symbol_ptr = in_symbol_ptr;
  while (*++next_symbol_ptr == BLANK);
  while (length) {
    if ((*next_symbol_ptr == 0x20) || (*next_symbol_ptr >= num_base_symbols)) {
      score_word();
      return;
    }
    length--;
    in_symbol_ptr = next_symbol_ptr;
    while (*++next_symbol_ptr == BLANK);
    string_entropy += log_num_symbols - log2((double)symbol_count[*in_symbol_ptr]);
    symbols_in_string++;
  }
  if ((*next_symbol_ptr == 0x20) || (*next_symbol_ptr >= num_base_symbols)) {  // calculate this child's score
    score_word();
    return;
  }
  search_symbol = *next_symbol_ptr;
  if ((S32)search_symbol >= 0) {
    node_ptr = &string_nodes[node_ptr->child_node_num];
    symbols_in_string++;
    in_symbol_ptr = next_symbol_ptr;
    if (search_symbol == node_ptr->symbol)
      goto found_sibling_w;
    if (node_ptr->sibling_node_num[search_symbol & 1]) {
      node_ptr = &string_nodes[node_ptr->sibling_node_num[search_symbol & 1]];
      goto find_sibling_w;
    }
  }
  return;
}


static inline void find_best_string(U32 *first_symbol_ptr, U8 save_scores)
{
  U32 * in_symbol_ptr = first_symbol_ptr;
  U32 first_symbol = *in_symbol_ptr;
  U32 symbols_in_string = 2;
  double string_entropy = log_num_symbols - log2((double)symbol_count[first_symbol]);

  best_score = 0.0;
  best_length = 0;
  found_new_rule = 0;
  while (*++in_symbol_ptr == BLANK);
  if ((S32)*in_symbol_ptr < 0)
    return;
  U32 search_symbol = *in_symbol_ptr;
  match_start_index = first_symbol_ptr - start_symbol_ptr;
  node_ptr = &string_nodes[base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)]];

find_sibling:
  find_base_node_sibling();

found_sibling:
  if (node_ptr->instances > 1) {
    string_entropy += log_num_symbols - log2((double)symbol_count[search_symbol]);
    U16 length = node_ptr->num_extra_symbols;
    symbols_in_string += length;
    while (length) {
      if (save_scores) {
        string_node_ptr[symbols_in_string - length] = node_ptr;
        string_score[symbols_in_string - length] = 0.0;
      }
      length--;
      while (*++in_symbol_ptr == BLANK);
      string_entropy += log_num_symbols - log2((double)symbol_count[*in_symbol_ptr]);
    }

    if (node_ptr->found_overlap == 0) {  // calculate this child's score
      double d_node_instances_m_1 = (double)(node_ptr->instances - 1);
      double profit_per_sub = string_entropy + log2(d_node_instances_m_1) - log_num_symbols_plus_tokenization_cost;
      double profit = profit_per_sub * d_node_instances_m_1 - production_cost;
      if (profit >= 0.0) {
        double d_score = profit * profit_per_sub * profit_per_sub * profit_per_sub / (string_entropy * string_entropy);
        if (save_scores) {
          string_node_ptr[symbols_in_string] = node_ptr;
          string_score[symbols_in_string] = d_score;
        }
        if (d_score > best_score) {
          best_score = d_score;
          best_length = symbols_in_string;
          best_node_ptr = node_ptr;
        }
      }
      else if (save_scores) {
        string_node_ptr[symbols_in_string] = node_ptr;
        string_score[symbols_in_string] = 0.0;
      }
    }
    else if (save_scores) {
      string_node_ptr[symbols_in_string] = node_ptr;
      string_score[symbols_in_string] = 0.0;
    }
    while (*++in_symbol_ptr == BLANK);
    search_symbol = *in_symbol_ptr;
    if ((S32)search_symbol >= 0) {
      node_ptr = &string_nodes[node_ptr->child_node_num];
      symbols_in_string++;
      if (search_symbol == node_ptr->symbol)
        goto found_sibling;
      if (node_ptr->sibling_node_num[search_symbol & 1]) {
        node_ptr = &string_nodes[node_ptr->sibling_node_num[search_symbol & 1]];
        goto find_sibling;
      }
    }
  }
  else if (save_scores) {
    string_node_ptr[symbols_in_string] = node_ptr;
    string_score[symbols_in_string] = 0.0;
  }
  if (best_length)
    found_new_rule = 1;
  return;
}


static inline void substitute(U32 * first_symbol_ptr)
{
  U32 search_symbol, first_symbol;
  U32 * string_ptr = first_symbol_ptr;
  U16 num_extra_symbols;
  struct string_node * parent_node_ptr;

  match_list_length = 0;
  get_string_starts(best_node_ptr->child_node_num);

  /* decrement instances for substituted string */
  symbol_ptr = start_symbol_ptr + match_list[0];
  first_symbol = *symbol_ptr;
  get_symbol(search_symbol);
  *++end_symbol_ptr = first_symbol;
  *++end_symbol_ptr = search_symbol;
  symbol_count[first_symbol] -= match_list_length - 1;
  symbol_count[search_symbol] -= match_list_length - 1;
  node_ptr = &string_nodes[base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)]];
  find_base_node_sibling();
  node_ptr->instances -= match_list_length - 1;
  U32 match_start_index = end_symbol_ptr - 1 - start_symbol_ptr;
  node_ptr->match_start_index = match_start_index;
  num_extra_symbols = node_ptr->num_extra_symbols;

  U16 length = 2;

  while (length++ < best_length) {
    if (num_extra_symbols == 0) {
      parent_node_ptr = node_ptr;
      node_ptr = &string_nodes[node_ptr->child_node_num];
      if (parent_node_ptr->instances == 1) {
        parent_node_ptr->child_node_num = 0;
        parent_node_ptr->num_extra_symbols = 0;
      }
      get_symbol(search_symbol);
      find_child_node_sibling();
      node_ptr->instances -= match_list_length - 1;
      node_ptr->match_start_index = match_start_index;
      num_extra_symbols = node_ptr->num_extra_symbols;
    }
    else {
      num_extra_symbols--;
      get_symbol(search_symbol);
    }
    symbol_count[search_symbol] -= match_list_length - 1;
    *++end_symbol_ptr = search_symbol;
  }
  *++end_symbol_ptr = 0x80000001 + num_rules;
  symbol_count[num_rules] = match_list_length;

  /* add prefixes starting with the rule for the match, move match child to rule child */
  U32 add_node_num = node_ptr->child_node_num;
  U32 next_add_node_num;
  if (num_extra_symbols == 0) {
    base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE] = string_nodes[add_node_num].sibling_node_num[0];
    base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE + 1]
        = string_nodes[add_node_num].sibling_node_num[1];
    U32 * prior_node_num_ptr
        = &base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE + (string_nodes[add_node_num].symbol & 1)];
    next_add_node_num = *prior_node_num_ptr;
    *prior_node_num_ptr = add_node_num;
    U8 symbol_shift = 0;
    while (next_add_node_num) {
      string_nodes[add_node_num].sibling_node_num[0] = string_nodes[next_add_node_num].sibling_node_num[0];
      string_nodes[add_node_num].sibling_node_num[1] = string_nodes[next_add_node_num].sibling_node_num[1];
      symbol_shift++;
      prior_node_num_ptr
          = &string_nodes[add_node_num].sibling_node_num[(string_nodes[next_add_node_num].symbol >> symbol_shift) & 1];
      add_node_num = next_add_node_num;
      next_add_node_num = *prior_node_num_ptr;
      *prior_node_num_ptr = add_node_num;
    }
    string_nodes[add_node_num].sibling_node_num[0] = 0;
    string_nodes[add_node_num].sibling_node_num[1] = 0;
  }
  else {
    search_symbol = *string_ptr;
    struct string_node * new_node_ptr = &string_nodes[next_string_node_num];
    write_node_ptr_data(new_node_ptr, search_symbol, node_ptr->match_start_index,
        string_nodes[add_node_num].sibling_node_num[0], string_nodes[add_node_num].sibling_node_num[1], match_list_length,
        node_ptr->child_node_num, num_extra_symbols - 1, node_ptr->found_overlap);
    if (search_symbol & 1) {
      base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE] = 0;
      base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE + 1] = next_string_node_num++;
    }
    else {
      base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE] = next_string_node_num++;
      base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE + 1] = 0;
    }
  }
  node_ptr->child_node_num = 0;
  node_ptr->num_extra_symbols = 0;
  num_in_symbols -= (match_list_length - 1) * (best_length - 1) - 2;
  new_symbol_index += best_length + 1;
  log_num_symbols = log2((double)num_in_symbols);
  log_num_symbols_plus_tokenization_cost = log_num_symbols + 1.4;

  while (match_list_length) {
    U32 * suffix_start_ptr = start_symbol_ptr + match_list[--match_list_length];
    *suffix_start_ptr = num_rules;
    U16 i = best_length - 2;
    do {
      while (*++suffix_start_ptr == BLANK);
      *suffix_start_ptr = BLANK;
    } while (i--);
  }
  num_rules++;
}


static inline void substitute_runs(U32 run_symbol)
{
  match_list_length = 0;
  get_run_string_starts(base_string_nodes_child_node_num[2 * run_symbol + (run_symbol & 1)]);

  U32 match_index_bits = 1;
  U32 temp_num_in_symbols = new_symbol_index;
  while (temp_num_in_symbols >>= 1)
    match_index_bits++;
  match_start_nodes[0].match_index = match_list[0];
  match_start_nodes[0].child_node_num1 = 0;
  match_start_nodes[0].child_node_num2 = 0;
  U32 match_num = 1;
  U32 match_start_node_num;

  while (match_num < match_list_length) {
    U32 match_index = match_list[match_num];
    U32 saved_match_index;
    U32 node_bit = match_index_bits - 1;
    match_start_node_num = 0;
    while (1) {
      if (match_index < match_start_nodes[match_start_node_num].match_index) {
        if (match_start_nodes[match_start_node_num].match_index & (1 << node_bit)) {
          saved_match_index = match_start_nodes[match_start_node_num].match_index;
          match_start_nodes[match_start_node_num].match_index = match_index;
          match_index = saved_match_index;
          if (match_start_nodes[match_start_node_num].child_node_num2 == 0) {
            match_start_nodes[match_start_node_num].child_node_num2 = match_num;
            match_start_nodes[match_num].match_index = match_index;
            match_start_nodes[match_num].child_node_num1 = 0;
            match_start_nodes[match_num++].child_node_num2 = 0;
            break;
          }
          else
            match_start_node_num = match_start_nodes[match_start_node_num].child_node_num2;
        }
        else {
          saved_match_index = match_start_nodes[match_start_node_num].match_index;
          match_start_nodes[match_start_node_num].match_index = match_index;
          match_index = saved_match_index;
          if (match_start_nodes[match_start_node_num].child_node_num1 == 0) {
            match_start_nodes[match_start_node_num].child_node_num1 = match_num;
            match_start_nodes[match_num].match_index = match_index;
            match_start_nodes[match_num].child_node_num1 = 0;
            match_start_nodes[match_num++].child_node_num2 = 0;
            break;
          }
          else
            match_start_node_num = match_start_nodes[match_start_node_num].child_node_num1;
        }
      }
      else {
        if (match_index & (1 << node_bit)) {
          if (match_start_nodes[match_start_node_num].child_node_num2 == 0) {
            match_start_nodes[match_start_node_num].child_node_num2 = match_num;
            match_start_nodes[match_num].match_index = match_index;
            match_start_nodes[match_num].child_node_num1 = 0;
            match_start_nodes[match_num++].child_node_num2 = 0;
            break;
          }
          else
            match_start_node_num = match_start_nodes[match_start_node_num].child_node_num2;
        }
        else {
          if (match_start_nodes[match_start_node_num].child_node_num1 == 0) {
            match_start_nodes[match_start_node_num].child_node_num1 = match_num;
            match_start_nodes[match_num].match_index = match_index;
            match_start_nodes[match_num].child_node_num1 = 0;
            match_start_nodes[match_num++].child_node_num2 = 0;
            break;
          }
          else
            match_start_node_num = match_start_nodes[match_start_node_num].child_node_num1;
        }
      }
      node_bit--;
    }
  }
  sorted_match_index = 0;
  sort_match_indexes(0);
  match_start_indexes[sorted_match_index] = end_symbol_ptr - start_symbol_ptr;
  U32 longest_match = 0;
  U32 second_longest_match = 0;
  U32 match_length = 2;
  for (match_num = 1 ; match_num <= sorted_match_index ; match_num++) {
    if (match_start_indexes[match_num] == match_start_indexes[match_num - 1] + 1)
      match_length++;
    else {
      if (match_length > second_longest_match) {
        if (match_length > longest_match) {
          second_longest_match = longest_match;
          longest_match = match_length;
        }
        else
          second_longest_match = match_length;
      }
      match_length = 2;
    }
  }
  longest_match >>= 1;
  if (second_longest_match > longest_match)
    longest_match = second_longest_match;
  U8 max_power_2_reduction = 0;
  U8 temp_power_reduction;
  while (longest_match >>= 1)
    max_power_2_reduction++;
  num_in_symbols += (best_length + 1) * max_power_2_reduction;
  for (temp_power_reduction = 0 ; temp_power_reduction < max_power_2_reduction ; temp_power_reduction++)
    symbol_count[num_rules + temp_power_reduction] = 0;

  for (match_num = 1 ; match_num <= sorted_match_index ; match_num++) {
    if (match_start_indexes[match_num] == match_start_indexes[match_num - 1] + 1)
      match_length++;
    else {
      U8 power_reduction = 0;
      U32 temp_match_length = match_length;
      while (temp_match_length >>= 1)
        power_reduction++;
      if (power_reduction > max_power_2_reduction)
        power_reduction = max_power_2_reduction;
      U32 * write_ptr = start_symbol_ptr + match_start_indexes[match_num - 1] - match_length + 2;
      U32 * end_write_ptr = write_ptr + match_length;
      temp_power_reduction = power_reduction;
      while (temp_power_reduction) {
        while (match_length >= (1U << temp_power_reduction)) {
          *write_ptr++ = num_rules + temp_power_reduction - 1;
          symbol_count[run_symbol] -= 1 << temp_power_reduction;
          symbol_count[num_rules + temp_power_reduction - 1]++;
          num_in_symbols -= (1 << temp_power_reduction) - 1;
          match_length -= 1 << temp_power_reduction;
        }
        temp_power_reduction--;
      }
      if (match_length)
        write_ptr++;
      while (write_ptr < end_write_ptr)
        *write_ptr++ = BLANK;
      match_length = 2;
    }
  }
  *++end_symbol_ptr = run_symbol;
  *++end_symbol_ptr = run_symbol;
  *++end_symbol_ptr = 0x80000001 + num_rules++;
  symbol_count[run_symbol] += 2;
  new_symbol_index += 3;
  temp_power_reduction = 2;
  while (temp_power_reduction <= max_power_2_reduction) {
    *++end_symbol_ptr = num_rules - 1;
    *++end_symbol_ptr = num_rules - 1;
    *++end_symbol_ptr = 0x80000001 + num_rules++;
    symbol_count[num_rules - 1] += 2;
    new_symbol_index += 3;
    temp_power_reduction++;
  }
}


static inline void substitute_and_update_tree(U32 * first_symbol_ptr)
{
  U32 search_symbol, end_match_child_num;
  U32 saved_match_start_index, first_symbol, back_node_num, max_back_node_depth;
  U32 * string_ptr = first_symbol_ptr;
  U16 num_extra_symbols;
  U8 end_match_found_overlap;

  match_list_length = 0;
  get_string_starts(best_node_ptr->child_node_num);
  S32 back_node_index = match_list[0];
  while (*(start_symbol_ptr + --back_node_index) == BLANK);

  /* build back node tree */
  initialize_back_node_data(1, *(start_symbol_ptr + back_node_index), back_node_index, 1);
  U32 num_back_nodes = 2;
  max_back_node_depth = 1;
  first_back_node_of_depth[1] = 0;
  U32 match_num = 1;
  do {
    U32 * search_symbol_ptr = start_symbol_ptr + match_list[match_num];
    while (*--search_symbol_ptr == BLANK);
    search_symbol = *search_symbol_ptr;
    U32 tree_node = 1;
    U32 back_node_depth = 1;
    while (1) {
      U32 shifted_search_symbol = search_symbol;
      while (back_nodes[tree_node].symbol != search_symbol) {
        if (back_nodes[tree_node].sibling_node_num[shifted_search_symbol & 1]) {
          tree_node = back_nodes[tree_node].sibling_node_num[shifted_search_symbol & 1];
          shifted_search_symbol >>= 1;
        }
        else {
          back_nodes[tree_node].sibling_node_num[shifted_search_symbol & 1] = num_back_nodes;
          initialize_back_node_data(num_back_nodes, search_symbol, search_symbol_ptr - start_symbol_ptr,
              back_node_depth);
          tree_node = num_back_nodes++;
          goto add_next_match;
        }
      }
      if (back_nodes[tree_node].instances++ == 1) {
        if (back_node_depth > max_back_node_depth)
          first_back_node_of_depth[++max_back_node_depth] = 0;
        back_nodes[tree_node].next_back_node_num = first_back_node_of_depth[back_node_depth];
        first_back_node_of_depth[back_node_depth] = tree_node;
        back_nodes[tree_node].child_node_num = num_back_nodes;
        back_node_index = back_nodes[tree_node].last_match_index;
        while (*(start_symbol_ptr + --back_node_index) == BLANK);
        initialize_back_node_data(num_back_nodes, *(start_symbol_ptr + back_node_index),
            back_node_index, back_node_depth + 1);
        tree_node = num_back_nodes++;
      }
      else
        tree_node = back_nodes[tree_node].child_node_num;
      while (*--search_symbol_ptr == BLANK);
      search_symbol = *search_symbol_ptr;
      back_node_depth++;
    }
add_next_match:
    match_num++;
  } while (match_num < match_list_length);

  U32 match_index_bits = 1;
  U32 temp_num_in_symbols = new_symbol_index;
  while (temp_num_in_symbols >>= 1)
    match_index_bits++;

  back_node_num = 0;
  while (back_nodes[++back_node_num].instances != 1);
  match_start_nodes[0].match_index = back_nodes[back_node_num].last_match_index;
  U32 back_depth;
  for (back_depth = 0 ; back_depth < back_nodes[back_node_num].depth ; back_depth++)
    while (*(start_symbol_ptr + ++match_start_nodes[0].match_index) == BLANK);
  match_start_nodes[0].depth = back_nodes[back_node_num].depth;
  match_start_nodes[0].child_node_num1 = 0;
  match_start_nodes[0].child_node_num2 = 0;

  /* sort match indexes */
  U32 num_singles = 1;
  U32 match_start_node_num;
  while (++back_node_num < num_back_nodes) {
    if (back_nodes[back_node_num].instances == 1) {
      U32 depth = back_nodes[back_node_num].depth;
      U32 match_index = back_nodes[back_node_num].last_match_index;
      U32 i;
      for (i = 0 ; i < depth ; i++)
        while (*(start_symbol_ptr + ++match_index) == BLANK);

      U32 saved_match_index, saved_depth;
      U32 node_bit = match_index_bits - 1;
      match_start_node_num = 0;
      while (1) {
        if (match_index < match_start_nodes[match_start_node_num].match_index) {
          if (match_start_nodes[match_start_node_num].match_index & (1 << node_bit)) {
            saved_match_index = match_start_nodes[match_start_node_num].match_index;
            match_start_nodes[match_start_node_num].match_index = match_index;
            match_index = saved_match_index;
            saved_depth = match_start_nodes[match_start_node_num].depth;
            match_start_nodes[match_start_node_num].depth = depth;
            depth = saved_depth;
            if (match_start_nodes[match_start_node_num].child_node_num2 == 0) {
              match_start_nodes[match_start_node_num].child_node_num2 = num_singles;
              match_start_nodes[num_singles].match_index = match_index;
              match_start_nodes[num_singles].depth = depth;
              match_start_nodes[num_singles].child_node_num1 = 0;
              match_start_nodes[num_singles++].child_node_num2 = 0;
              break;
            }
            else
              match_start_node_num = match_start_nodes[match_start_node_num].child_node_num2;
          }
          else {
            saved_match_index = match_start_nodes[match_start_node_num].match_index;
            match_start_nodes[match_start_node_num].match_index = match_index;
            match_index = saved_match_index;
            saved_depth = match_start_nodes[match_start_node_num].depth;
            match_start_nodes[match_start_node_num].depth = depth;
            depth = saved_depth;
            if (match_start_nodes[match_start_node_num].child_node_num1 == 0) {
              match_start_nodes[match_start_node_num].child_node_num1 = num_singles;
              match_start_nodes[num_singles].match_index = match_index;
              match_start_nodes[num_singles].depth = depth;
              match_start_nodes[num_singles].child_node_num1 = 0;
              match_start_nodes[num_singles++].child_node_num2 = 0;
              break;
            }
            else
              match_start_node_num = match_start_nodes[match_start_node_num].child_node_num1;
          }
        }
        else {
          if (match_index & (1 << node_bit)) {
            if (match_start_nodes[match_start_node_num].child_node_num2 == 0) {
              match_start_nodes[match_start_node_num].child_node_num2 = num_singles;
              match_start_nodes[num_singles].match_index = match_index;
              match_start_nodes[num_singles].depth = depth;
              match_start_nodes[num_singles].child_node_num1 = 0;
              match_start_nodes[num_singles++].child_node_num2 = 0;
              break;
            }
            else
              match_start_node_num = match_start_nodes[match_start_node_num].child_node_num2;
          }
          else {
            if (match_start_nodes[match_start_node_num].child_node_num1 == 0) {
              match_start_nodes[match_start_node_num].child_node_num1 = num_singles;
              match_start_nodes[num_singles].match_index = match_index;
              match_start_nodes[num_singles].depth = depth;
              match_start_nodes[num_singles].child_node_num1 = 0;
              match_start_nodes[num_singles++].child_node_num2 = 0;
              break;
            }
            else
              match_start_node_num = match_start_nodes[match_start_node_num].child_node_num1;
          }
        }
        node_bit--;
      }
    }
  }

  U32 * end_suffix_symbol_ptr;
  U32 i;
  U32 i2 = 0;
  U32 match_start_node_num_array[32];
  U8 match_start_node_num_array_child_num[32];
  U8 depth = 0;
  match_start_node_num = 0;
  find_last_start_match_node();

  /* remove single instance back nodes via match start nodes, save indexes */
  while (1) {
    U32 check_depth = match_start_nodes[match_start_node_num].depth;
    match_start_index = match_start_nodes[match_start_node_num].match_index;
    match_start_indexes[++i2] = match_start_index;
    U32 * start_string_ptr = start_symbol_ptr + match_start_index;
    for (i = check_depth - 1 ; i != 0 ; i--)
      while (*--start_string_ptr == BLANK);

check_prior_start:
    while (1) {
      symbol_ptr = start_string_ptr;
      while (*--start_string_ptr == BLANK);
      U32 first_symbol = *start_string_ptr;
      if (first_symbol & 0x80000000)
        goto get_next_single;
      search_symbol = *symbol_ptr;
      prior_node_num_ptr = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)];
      node_ptr = &string_nodes[*prior_node_num_ptr];
      find_base_node_sibling_save_prior();

      struct string_node * root_match_node_ptr;
      if (check_depth == 1) {
        if (--node_ptr->instances == 0) {
          saved_match_start_index = node_ptr->match_start_index;
          free_node_ptr = node_ptr;
          remove_node();
          if (node_ptr->instances == 0)
            *prior_node_num_ptr = 0;
          prior_node_num_ptr = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (num_rules & 1)];
          if (*prior_node_num_ptr == 0)
            *prior_node_num_ptr = free_node_ptr - string_nodes;
          else {
            node_ptr = &string_nodes[*prior_node_num_ptr];
            shifted_search_symbol = num_rules >> 1;
            prior_node_num_ptr = &node_ptr->sibling_node_num[shifted_search_symbol & 1];
            find_last_sibling();
            *prior_node_num_ptr = free_node_ptr - string_nodes;
          }
          write_node_ptr_data(free_node_ptr, num_rules, saved_match_start_index, 0, 0, 1, 0, 0, 0);
          check_depth++;
          goto check_prior_start;
        }
        first_single_instance_node_ptr = 0;
        root_match_node_ptr = &string_nodes[*prior_node_num_ptr];
        while (*++symbol_ptr == BLANK);
        num_extra_symbols = root_match_node_ptr->num_extra_symbols;
        while (num_extra_symbols--)
          while (*++symbol_ptr == BLANK);
        if (node_ptr->instances == 1) {
          search_symbol = *symbol_ptr;
          prior_node_num_ptr = &node_ptr->child_node_num;
          node_ptr = &string_nodes[*prior_node_num_ptr];
          if (search_symbol == node_ptr->symbol) {
            if (node_ptr->sibling_node_num[0])
              *prior_node_num_ptr = node_ptr->sibling_node_num[0];
            else
              *prior_node_num_ptr = node_ptr->sibling_node_num[1];
            saved_match_start_index = node_ptr->match_start_index;
            free_node_ptr = node_ptr;
          }
          else {
            if (node_ptr->sibling_node_num[0]) {
              saved_match_start_index = string_nodes[node_ptr->sibling_node_num[0]].match_start_index;
              free_node_ptr = &string_nodes[node_ptr->sibling_node_num[0]];
              node_ptr->sibling_node_num[0] = 0;
            }
            else {
              saved_match_start_index = string_nodes[node_ptr->sibling_node_num[1]].match_start_index;
              free_node_ptr = &string_nodes[node_ptr->sibling_node_num[1]];
              node_ptr->sibling_node_num[1] = 0;
            }
          }
          shifted_search_symbol = num_rules;
          prior_node_num_ptr
              = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (num_rules & 1)];
          find_last_sibling();
          *prior_node_num_ptr = free_node_ptr - string_nodes;
          write_node_ptr_data(free_node_ptr, num_rules, saved_match_start_index, 0, 0, 1, 0, 0, 0);
          check_depth++;
          goto check_prior_start;
        }
      }
      else {
        if (node_ptr->child_node_num == 0)
          goto get_next_single;
        while (*++symbol_ptr == BLANK);
        first_single_instance_node_ptr = 0;
        num_extra_symbols = node_ptr->num_extra_symbols;
        while (symbol_ptr < start_symbol_ptr + match_start_index) {
          if (num_extra_symbols == 0) {
            search_symbol = *symbol_ptr;
            node_ptr = &string_nodes[node_ptr->child_node_num];
            find_child_node_sibling();
            if (node_ptr->child_node_num == 0)
              goto get_next_single;
            num_extra_symbols = node_ptr->num_extra_symbols;
          }
          else
            num_extra_symbols--;
          while (*++symbol_ptr == BLANK);
        }

        if (num_extra_symbols) { // insert node in branch
          U32 new_string_node_num;
          if (free_nodes_list_length)
            new_string_node_num = free_nodes_list[--free_nodes_list_length];
          else
            new_string_node_num = next_string_node_num++;
          struct string_node * new_node_ptr = &string_nodes[new_string_node_num];
          write_node_ptr_data(new_node_ptr, *symbol_ptr, node_ptr->match_start_index, 0, 0,
              node_ptr->instances, node_ptr->child_node_num, num_extra_symbols - 1, node_ptr->found_overlap);
          node_ptr->num_extra_symbols -= num_extra_symbols;
          node_ptr->child_node_num = new_string_node_num;
        }
        root_match_node_ptr = &string_nodes[node_ptr->child_node_num];
      }

      search_symbol = *symbol_ptr;
      prior_node_num_ptr = &node_ptr->child_node_num;
      node_ptr = &string_nodes[*prior_node_num_ptr];
      find_child_node_sibling();
      if (--node_ptr->instances == 0) {
        saved_match_start_index = node_ptr->match_start_index;
        free_node_ptr = node_ptr;
        remove_node();
        if (node_ptr->instances == 0)
          *prior_node_num_ptr = 0;

        if (check_depth == 1)
          prior_node_num_ptr = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (num_rules & 1)];
        else {
          if (root_match_node_ptr->instances == 0) {
            check_depth++;
            goto check_prior_start;
          }
          prior_node_num_ptr = &root_match_node_ptr->sibling_node_num[num_rules & 1];
        }
        shifted_search_symbol = num_rules;
        find_last_sibling();
        *prior_node_num_ptr = free_node_ptr - string_nodes;
        write_node_ptr_data(free_node_ptr, num_rules, saved_match_start_index, 0, 0, 1, 0, 0, 0);
        check_depth++;
        goto check_prior_start;
      }
      while (*++symbol_ptr == BLANK);
      if (node_ptr->instances == 1) {
        if (string_nodes[node_ptr->child_node_num].instances == 1) {
          first_single_instance_node_ptr = node_ptr;
          num_extra_symbols = node_ptr->num_extra_symbols;
          while (num_extra_symbols--)
            while (*++symbol_ptr == BLANK);
          node_ptr = &string_nodes[node_ptr->child_node_num];
          free_node_ptr = node_ptr;
          if (*symbol_ptr == node_ptr->symbol) {
            saved_match_start_index = node_ptr->match_start_index;
            if (node_ptr->sibling_node_num[0]) {
              first_single_instance_node_ptr->match_start_index = string_nodes[node_ptr->sibling_node_num[0]].match_start_index;
              if (free_nodes_list_length < FREE_NODES_LIST_SIZE)
                free_nodes_list[free_nodes_list_length++] = node_ptr->sibling_node_num[0];
            }
            else {
              first_single_instance_node_ptr->match_start_index = string_nodes[node_ptr->sibling_node_num[1]].match_start_index;
              if (free_nodes_list_length < FREE_NODES_LIST_SIZE)
                free_nodes_list[free_nodes_list_length++] = node_ptr->sibling_node_num[1];
            }
          }
          else {
            first_single_instance_node_ptr->match_start_index = node_ptr->match_start_index;
            if (node_ptr->sibling_node_num[0]) {
              saved_match_start_index = string_nodes[node_ptr->sibling_node_num[0]].match_start_index;
              if (free_nodes_list_length < FREE_NODES_LIST_SIZE)
                free_nodes_list[free_nodes_list_length++] = node_ptr->sibling_node_num[0];
            }
            else {
              saved_match_start_index = string_nodes[node_ptr->sibling_node_num[1]].match_start_index;
              if (free_nodes_list_length < FREE_NODES_LIST_SIZE)
                free_nodes_list[free_nodes_list_length++] = node_ptr->sibling_node_num[1];
            }
          }
          first_single_instance_node_ptr->child_node_num = 0;
          first_single_instance_node_ptr->num_extra_symbols = 0;
          shifted_search_symbol = num_rules;
          if (check_depth > 1)
            prior_node_num_ptr = &root_match_node_ptr->sibling_node_num[shifted_search_symbol & 1];
          else
            prior_node_num_ptr
                = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (num_rules & 1)];
          find_last_sibling();
          *prior_node_num_ptr = free_node_ptr - string_nodes;
          write_node_ptr_data(free_node_ptr, num_rules, saved_match_start_index, 0, 0, 1, 0, 0, 0);
          check_depth++;
          goto check_prior_start;
        }
        if (first_single_instance_node_ptr == 0)
          first_single_instance_node_ptr = node_ptr;
      }

      while (1) {
        num_extra_symbols = node_ptr->num_extra_symbols;
        while (num_extra_symbols--)
          while (*++symbol_ptr == BLANK);
        prior_node_num_ptr = &node_ptr->child_node_num;
        node_ptr = &string_nodes[node_ptr->child_node_num];
        search_symbol = *symbol_ptr;
        find_child_node_sibling_save_prior();
        if (--node_ptr->instances == 0) {
          saved_match_start_index = node_ptr->match_start_index;
          free_node_ptr = node_ptr;
          remove_node();

          if (node_ptr->instances == 0) {
            *prior_node_num_ptr = 0;
            if (first_single_instance_node_ptr) {
              first_single_instance_node_ptr->match_start_index = prior_node_ptr->match_start_index;
              first_single_instance_node_ptr->child_node_num = 0;
              first_single_instance_node_ptr->num_extra_symbols = 0;
            }
          }
          else {
            if (first_single_instance_node_ptr) {
              first_single_instance_node_ptr->match_start_index = node_ptr->match_start_index;
              first_single_instance_node_ptr->child_node_num = 0;
              first_single_instance_node_ptr->num_extra_symbols = 0;
            }
          }
          shifted_search_symbol = num_rules;
          if (check_depth > 1)
            prior_node_num_ptr = &root_match_node_ptr->sibling_node_num[shifted_search_symbol & 1];
          else
            prior_node_num_ptr
                = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (num_rules & 1)];
          find_last_sibling();
          *prior_node_num_ptr = free_node_ptr - string_nodes;
          write_node_ptr_data(free_node_ptr, num_rules, saved_match_start_index, 0, 0, 1, 0, 0, 0);
          check_depth++;
          goto check_prior_start;
        }
        if (node_ptr->instances == 1) {
          if (first_single_instance_node_ptr == 0)
           first_single_instance_node_ptr = node_ptr;
        }
        while (*++symbol_ptr == BLANK);
      }
      check_depth++;
    }


get_next_single:
    if (depth == 0)
      break;
    match_start_node_num = match_start_node_num_array[--depth];
    if (match_start_node_num_array_child_num[depth]) {
      if (match_start_nodes[match_start_node_num].child_node_num1) {
        match_start_node_num_array_child_num[depth++] = 0;
        match_start_node_num = match_start_nodes[match_start_node_num].child_node_num1;
        find_last_start_match_node();
      }
    }
  }

  /* subtract >1 instance back node instances */
  match_start_indexes[0] = new_symbol_index + 1;
  U32 * end_match_symbol_ptr;
  U32 back_node_depth;
  U32 sum_inst = 0;
  back_node_depth = max_back_node_depth;
  do {
    back_node_num = first_back_node_of_depth[back_node_depth];
    while (back_node_num) {
      first_single_instance_node_ptr = 0;
      symbol_ptr = start_symbol_ptr + back_nodes[back_node_num].last_match_index;
      first_symbol = *symbol_ptr;
      get_symbol(search_symbol);

      prior_node_num_ptr = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)];
      node_ptr = &string_nodes[*prior_node_num_ptr];
      U8 found_first_free_node = 0;
      if (back_node_depth >= 2) {
        find_base_node_sibling_save_prior();
        num_extra_symbols = node_ptr->num_extra_symbols;
        U32 num_symbols = 2;
        while (num_symbols != back_node_depth) {
          num_symbols++;
          if (num_extra_symbols) {
            num_extra_symbols--;
            while (*++symbol_ptr == BLANK);
          }
          else {
            node_ptr = &string_nodes[node_ptr->child_node_num];
            get_symbol(search_symbol);
            find_child_node_sibling();
            num_extra_symbols = node_ptr->num_extra_symbols;
          }
        }
        U32 before_match_node_num = node_ptr - string_nodes;
        U32 next_child_node_num;

        if (num_extra_symbols >= best_length)
          node_ptr->num_extra_symbols -= best_length - 1;
        else {
          if (num_extra_symbols) {
            U32 new_string_node_num;
            if (free_nodes_list_length)
              new_string_node_num = free_nodes_list[--free_nodes_list_length];
            else
              new_string_node_num = next_string_node_num++;
            struct string_node * new_node_ptr = &string_nodes[new_string_node_num];
            write_node_ptr_data(new_node_ptr, *string_ptr, node_ptr->match_start_index, 0, 0,
                node_ptr->instances, node_ptr->child_node_num, num_extra_symbols - 1, node_ptr->found_overlap);
            node_ptr->num_extra_symbols -= num_extra_symbols;
            node_ptr->child_node_num = new_string_node_num;
            num_extra_symbols = 0;
          }
          next_child_node_num = node_ptr->child_node_num;
          while (num_symbols != back_node_depth + best_length) {
            num_symbols++;
            if (num_extra_symbols) {
              num_extra_symbols--;
              while (*++symbol_ptr == BLANK);
            }
            else {
              prior_node_num_ptr = &node_ptr->child_node_num;
              node_ptr = &string_nodes[next_child_node_num];
              get_symbol(search_symbol);
              find_child_node_sibling_save_prior();
              node_ptr->instances -= back_nodes[back_node_num].instances;
              next_child_node_num = node_ptr->child_node_num;
              num_extra_symbols = node_ptr->num_extra_symbols;
              if (node_ptr->instances == 0) {
                saved_match_start_index = node_ptr->match_start_index;
                end_match_child_num = node_ptr->child_node_num;
                end_match_found_overlap = node_ptr->found_overlap;
                free_node_ptr = node_ptr;
                remove_node();
                if (found_first_free_node == 0) {
                  found_first_free_node = 1;
                  if (node_ptr->instances == 0) {
                    *prior_node_num_ptr = 0;
                    if (first_single_instance_node_ptr) {
                      first_single_instance_node_ptr->match_start_index = prior_node_ptr->match_start_index;
                      first_single_instance_node_ptr->child_node_num = 0;
                      first_single_instance_node_ptr->num_extra_symbols = 0;
                    }
                  }
                  else
                    if (first_single_instance_node_ptr) {
                      first_single_instance_node_ptr->match_start_index = node_ptr->match_start_index;
                      first_single_instance_node_ptr->child_node_num = 0;
                      first_single_instance_node_ptr->num_extra_symbols = 0;
                    }
                }
              }
              else if ((node_ptr->instances == 1) && (first_single_instance_node_ptr == 0))
                first_single_instance_node_ptr = node_ptr;
            }
          }
          if (string_nodes[before_match_node_num].child_node_num == 0)
            string_nodes[before_match_node_num].child_node_num = free_node_ptr - string_nodes;
          else {
            node_ptr = &string_nodes[string_nodes[before_match_node_num].child_node_num];
            shifted_search_symbol = num_rules;
            prior_node_num_ptr = &node_ptr->sibling_node_num[shifted_search_symbol & 1];
            find_last_sibling();
            *prior_node_num_ptr = free_node_ptr - string_nodes;
          }
          write_node_ptr_data(free_node_ptr, num_rules, saved_match_start_index, 0, 0, back_nodes[back_node_num].instances,
              end_match_child_num, num_extra_symbols, end_match_found_overlap);
        }
      }
      else {
        find_base_node_sibling_save_prior();
        node_ptr->instances -= back_nodes[back_node_num].instances;
        num_extra_symbols = node_ptr->num_extra_symbols;
        U32 next_child_node_num = node_ptr->child_node_num;
        if (node_ptr->instances == 0) {
          saved_match_start_index = node_ptr->match_start_index;
          end_match_child_num = node_ptr->child_node_num;
          end_match_found_overlap = node_ptr->found_overlap;
          free_node_ptr = node_ptr;
          remove_node();
          if (node_ptr->instances == 0)
            *prior_node_num_ptr = 0;
          found_first_free_node = 1;
        }
        else if (node_ptr->instances == 1)
          first_single_instance_node_ptr = node_ptr;
        end_suffix_symbol_ptr = start_symbol_ptr + back_nodes[back_node_num].last_match_index;
        for (i = 0 ; i < best_length ; i++)
          while (*++end_suffix_symbol_ptr == BLANK);
        while (symbol_ptr < end_suffix_symbol_ptr) {
          if (num_extra_symbols) {
            num_extra_symbols--;
            while (*++symbol_ptr == BLANK);
          }
          else {
            prior_node_num_ptr = &node_ptr->child_node_num;
            node_ptr = &string_nodes[next_child_node_num];
            get_symbol(search_symbol);
            find_child_node_sibling_save_prior();
            node_ptr->instances -= back_nodes[back_node_num].instances;
            next_child_node_num = node_ptr->child_node_num;
            num_extra_symbols = node_ptr->num_extra_symbols;
            if (node_ptr->instances == 0) {
              end_match_child_num = node_ptr->child_node_num;
              end_match_found_overlap = node_ptr->found_overlap;
              if (found_first_free_node) {
                if (free_nodes_list_length < FREE_NODES_LIST_SIZE)
                  free_nodes_list[free_nodes_list_length++] = free_node_ptr - string_nodes;
                free_node_ptr = node_ptr;
                remove_node();
              }
              else {
                found_first_free_node = 1;
                free_node_ptr = node_ptr;
                remove_node();
                if (node_ptr->instances == 0) {
                  *prior_node_num_ptr = 0;
                  if (first_single_instance_node_ptr) {
                    first_single_instance_node_ptr->match_start_index = prior_node_ptr->match_start_index;
                    first_single_instance_node_ptr->child_node_num = 0;
                    first_single_instance_node_ptr->num_extra_symbols = 0;
                  }
                }
                else {
                  if (first_single_instance_node_ptr) {
                    first_single_instance_node_ptr->match_start_index = node_ptr->match_start_index;
                    first_single_instance_node_ptr->child_node_num = 0;
                    first_single_instance_node_ptr->num_extra_symbols = 0;
                  }
                }
              }
            }
            else if ((node_ptr->instances == 1) && (first_single_instance_node_ptr == 0))
              first_single_instance_node_ptr = node_ptr;
          }
        }

        if (base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (num_rules & 1)] == 0)
          base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (num_rules & 1)]
              = free_node_ptr - string_nodes;
        else {
          node_ptr
              = &string_nodes[base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (num_rules & 1)]];
          shifted_search_symbol = num_rules >> 1;
          prior_node_num_ptr = &node_ptr->sibling_node_num[shifted_search_symbol & 1];
          find_last_sibling();
          *prior_node_num_ptr = free_node_ptr - string_nodes;
        }
        write_node_ptr_data(free_node_ptr, num_rules, saved_match_start_index, 0, 0, back_nodes[back_node_num].instances,
            end_match_child_num, num_extra_symbols, end_match_found_overlap);
      }
      sum_inst += back_nodes[back_node_num].instances;
      back_node_num = back_nodes[back_node_num].next_back_node_num;
    }
  } while (--back_node_depth);

  /* remove first match non-first, non-last match symbol suffixes, add new rule suffixes */
  match_start_index = match_start_indexes[match_list_length];
  U32 * suffix_start_ptr = start_symbol_ptr + match_start_index;
  U32 suffix_length = best_length;
  U32 suffix_index = 1;
  end_match_symbol_ptr = suffix_start_ptr;
  for (i = 0 ; i < best_length ; i++)
    while (*++end_match_symbol_ptr == BLANK);
 
  U16 saved_num_extra_symbols;
  while (suffix_index + 1 < best_length) {
    while (*++suffix_start_ptr == BLANK);
    suffix_length--;
    find_end_match_node_ptr_wd(suffix_start_ptr,suffix_length);
    if (first_single_instance_node_ptr) {
      first_single_instance_node_ptr->match_start_index = new_symbol_index + suffix_index + 1;
      first_single_instance_node_ptr->child_node_num = 0;
      first_single_instance_node_ptr->num_extra_symbols = 0;
    }
    else {
      next_match_index_index = match_list_length - 1;
      remove_match_suffix();
      add_match_suffix(); /* suffix for new rule */

      /* remove non-first match non-first, non-last match symbol suffixes (except first match) */
      U32 * temp_suffix_start_ptr = start_symbol_ptr + match_start_indexes[match_list_length];
      for (i = 0 ; i < suffix_index ; i++)
        while (*++temp_suffix_start_ptr == BLANK);
      U32 temp_suffix_length = best_length - suffix_index;
      find_end_match_node_ptr(temp_suffix_start_ptr,temp_suffix_length);
      U32 * save_end_match_symbol_ptr = end_match_symbol_ptr;
      saved_num_extra_symbols = num_extra_symbols;
      i2 = match_list_length - 1;
      while (i2) {
        num_extra_symbols = saved_num_extra_symbols;
        end_match_symbol_ptr = start_symbol_ptr + match_start_indexes[i2--];
        next_match_index_index = i2;
        for (i = 0 ; i < best_length ; i++)
          while (*++end_match_symbol_ptr == BLANK);
        first_single_instance_node_ptr = 0;
        remove_match_suffix();
        if (free_nodes_list_length < FREE_NODES_LIST_SIZE)
          free_nodes_list[free_nodes_list_length++] = free_node_ptr - string_nodes;
      }
      end_match_symbol_ptr = save_end_match_symbol_ptr;
    }
    suffix_index++;
  }

  /* remove first match last match symbol suffix, add new rule suffix, move last match symbol child branch */
  suffix_start_ptr = start_symbol_ptr + match_start_index;
  for (i = 0 ; i < suffix_index ; i++)
    while (*++suffix_start_ptr == BLANK);
  next_match_index_index = match_list_length - 1;
  remove_match_suffix_1(suffix_start_ptr);
  add_match_suffix_1(suffix_start_ptr);

  /* remove non-first match last match symbol suffixes */
  i2 = match_list_length - 1;
  while (i2) {
    suffix_start_ptr = start_symbol_ptr + match_start_indexes[i2--];
    for (i = 0 ; i < suffix_index ; i++)
      while (*++suffix_start_ptr == BLANK);
    next_match_index_index = i2;
    remove_match_suffix_1(suffix_start_ptr);
    if (free_nodes_list_length < FREE_NODES_LIST_SIZE)
      free_nodes_list[free_nodes_list_length++] = free_node_ptr - string_nodes;
  }

  /* decrement instances for substituted string */
  symbol_ptr = start_symbol_ptr + match_start_indexes[1];
  first_symbol = *symbol_ptr;
  get_symbol(search_symbol);
  *++end_symbol_ptr = first_symbol;
  *++end_symbol_ptr = search_symbol;
  symbol_count[first_symbol] -= match_list_length - 1;
  symbol_count[search_symbol] -= match_list_length - 1;
  prior_node_num_ptr = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)];
  node_ptr = &string_nodes[*prior_node_num_ptr];
  find_base_node_sibling();
  node_ptr->instances -= match_list_length - 1;
  U32 match_start_index = end_symbol_ptr - 1 - start_symbol_ptr;
  node_ptr->match_start_index = match_start_index;
  num_extra_symbols = node_ptr->num_extra_symbols;

  struct string_node * parent_node_ptr;
  U16 length = 2;
  while (length++ < best_length) {
    if (num_extra_symbols == 0) {
      parent_node_ptr = node_ptr;
      node_ptr = &string_nodes[node_ptr->child_node_num];
      if (parent_node_ptr->instances == 1) {
        parent_node_ptr->child_node_num = 0;
        parent_node_ptr->num_extra_symbols = 0;
      }
      get_symbol(search_symbol);
      find_child_node_sibling();
      node_ptr->instances -= match_list_length - 1;
      node_ptr->match_start_index = match_start_index;
      num_extra_symbols = node_ptr->num_extra_symbols;
    }
    else {
      num_extra_symbols--;
      get_symbol(search_symbol);
    }
    symbol_count[search_symbol] -= match_list_length - 1;
    *++end_symbol_ptr = search_symbol;
  }
  *++end_symbol_ptr = 0x80000001 + num_rules;
  symbol_count[num_rules] = match_list_length;

  /* add prefixes starting with the rule for the match, move match child to rule child */
  U32 add_node_num = node_ptr->child_node_num;
  U32 next_add_node_num;
  U32 * prior_node_num_ptr;
  base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE] = string_nodes[add_node_num].sibling_node_num[0];
  base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE + 1]
      = string_nodes[add_node_num].sibling_node_num[1];
  prior_node_num_ptr
      = &base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE + (string_nodes[add_node_num].symbol & 1)];
  next_add_node_num = *prior_node_num_ptr;
  *prior_node_num_ptr = add_node_num;
  U8 symbol_shift = 0;
  while (next_add_node_num) {
    string_nodes[add_node_num].sibling_node_num[0] = string_nodes[next_add_node_num].sibling_node_num[0];
    string_nodes[add_node_num].sibling_node_num[1] = string_nodes[next_add_node_num].sibling_node_num[1];
    symbol_shift++;
    prior_node_num_ptr
        = &string_nodes[add_node_num].sibling_node_num[(string_nodes[next_add_node_num].symbol >> symbol_shift) & 1];
    add_node_num = next_add_node_num;
    next_add_node_num = *prior_node_num_ptr;
    *prior_node_num_ptr = add_node_num;
  }
  string_nodes[add_node_num].sibling_node_num[0] = 0;
  string_nodes[add_node_num].sibling_node_num[1] = 0;

  node_ptr->child_node_num = 0;
  node_ptr->num_extra_symbols = 0;

  num_in_symbols -= (match_list_length - 1) * (best_length - 1) - 2;
  new_symbol_index += best_length + 1;
  log_num_symbols = log2((double)num_in_symbols);
  log_num_symbols_plus_tokenization_cost = log_num_symbols + 1.4;

  do {
    suffix_start_ptr = start_symbol_ptr + match_start_indexes[match_list_length--];
    *suffix_start_ptr = num_rules;
    U32 i;
    for (i = 1 ; i != best_length ; i++) {
      while (*(++suffix_start_ptr) == BLANK);
      *suffix_start_ptr = BLANK;
    }
  } while (match_list_length);
  num_rules++;
}


int main(int argc, char* argv[])
{
  FILE *fd_in, *fd_out;
  U64 *symbol_count_ptr, *base_node_ptr;
  U32 in_size, arg_num, UTF8_value, max_UTF8_value, symbol;
  U8 UTF8_compliant, cap_encoded, this_char, delta_gap;
  U8 *write_ptr;
  S8 out_file_name[50];
  double order_0_entropy, d_symbol_count, production_cost_paragraphs, production_cost_words, production_cost_chars;
  clock_t old_time, new_time, start_time;

  start_time = clock();

  production_cost_paragraphs = -1.0;
  production_cost_words = -1.0;
  production_cost_chars = 4.5;
  string_score[1] = 0.0;
  arg_num = 1;
  while (*argv[arg_num] ==  '-') {
    if (*(argv[arg_num]+1) == 'p') {
      production_cost_paragraphs = (double)atof(argv[arg_num++]+2);
      if ((production_cost_paragraphs < 1.4) && (production_cost_paragraphs != 0.0)) {
        fprintf(stderr,"ERROR: positive -p values must be >= 1.4 or use 0.0 to disable\n");
        exit(0);
      }
    }
    else if (*(argv[arg_num]+1) == 'w') {
      production_cost_words = (double)atof(argv[arg_num++]+2);
      if ((production_cost_words < 1.4) && (production_cost_words != 0.0)) {
        fprintf(stderr,"ERROR: positive -w values must be >= 1.4 or use 0.0 to disable\n");
        exit(0);
      }
    }
    else if (*(argv[arg_num]+1) == 'c') {
      production_cost_chars = (double)atof(argv[arg_num++]+2);
      if ((production_cost_chars < 1.4) && (production_cost_chars != 0.0)) {
        fprintf(stderr,"ERROR: positive -c values must be >= 1.4 or use 0.0 to disable\n");
        exit(0);
      }
    }
    else {
      fprintf(stderr,"ERROR - Invalid '-' format.  Only -p<value>, -w<value>, and -c<value> allowed\n");
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

  back_nodes = (struct back_node *)malloc(sizeof(struct back_node) * (in_size >> 3) + 100000);
  match_start_nodes = (struct match_start_node *)malloc(sizeof(struct match_start_node) * (in_size >> 5) + 30000);
  match_list = (U32 *)malloc(sizeof(U32) * (in_size >> 5) + 30000);
  if ((back_nodes == 0) || (match_start_nodes == 0) || (match_list == 0)) {
    fprintf(stderr,"Malloc failed\n");
    exit(0);
  }

  start_symbol_ptr = (U32 *)malloc(5 * ((size_t)in_size + 1000));
  if (start_symbol_ptr == 0) {
    fprintf(stderr,"ERROR - Insufficient RAM to compress - unable to allocate %Iu bytes for input data\n",
        5 * ((size_t)in_size + 1000));
    exit(0);
  }

  *start_symbol_ptr++ = EOF_SYMBOL;
  in_symbol_ptr = start_symbol_ptr;

  char_buffer = (U8 *)start_symbol_ptr + 4 * in_size;
  i1 = fread(char_buffer,1,in_size,fd_in);
  fflush(fd_in);
  fclose(fd_in);
  fprintf(stderr,"Read %u byte input file\n",(unsigned int)i1);

  // parse the file to determine UTF8_compliant
  UTF8_compliant = 1;
  cap_encoded = *char_buffer & 1;
  delta_gap = *char_buffer >> 1;
  in_char_ptr = char_buffer + 1;
  end_char_ptr = char_buffer + in_size;
  if (in_char_ptr >= end_char_ptr)
    goto write_file;

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

  fprintf(stderr,"capital encoded: %u, UTF-8 compliant %u\n",(unsigned int)cap_encoded,(unsigned int)UTF8_compliant);

  // parse the file to determine num_rules_defined and max_UTF8_value, convert characters to symbols
  num_rules_defined = 0;
  in_char_ptr = char_buffer + 1;

  if (UTF8_compliant) {
    num_base_symbols = START_MY_SYMBOLS;
    max_UTF8_value = 0;
    while (in_char_ptr != end_char_ptr) {
      this_char = *in_char_ptr++;
      if (this_char < 0x80)
        *in_symbol_ptr++ = (U32)this_char;
      else if (this_char == INSERT_SYMBOL_CHAR) {
        *in_symbol_ptr++ = START_MY_SYMBOLS + 0x10000 * (U32)*in_char_ptr
            + 0x100 * (U32)*(in_char_ptr+1) + (U32)*(in_char_ptr+2);
        in_char_ptr += 3;
      }
      else if (this_char == DEFINE_SYMBOL_CHAR) {
        *in_symbol_ptr++ = 0x80000000 + START_MY_SYMBOLS + 0x10000 * (U32)*in_char_ptr
            + 0x100 * (U32)*(in_char_ptr+1) + (U32)*(in_char_ptr+2);
        in_char_ptr += 3;
        num_rules_defined++;
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
    }
    fprintf(stderr,"Maximum unicode value 0x%x\n",(unsigned int)max_UTF8_value);
  }
  else {
    num_base_symbols = 0x100;
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
            *in_symbol_ptr++ = 0x100 + 0x10000 * (U32)*in_char_ptr
                + 0x100 * (U32)*(in_char_ptr+1) + (U32)*(in_char_ptr+2);
          else {
            *in_symbol_ptr++ = 0x80000000 + 0x100 + 0x10000 * (U32)*in_char_ptr
                + 0x100 * (U32)*(in_char_ptr+1) + (U32)*(in_char_ptr+2);
            num_rules_defined++;
          }
          in_char_ptr += 3;
        }
      }
    }
  }
  num_in_symbols = in_symbol_ptr - start_symbol_ptr;
  new_symbol_index = num_in_symbols;
  fprintf(stderr,"Found %u symbols, %u defines\n",(unsigned int)num_in_symbols,(unsigned int)num_rules_defined);
  end_symbol_ptr = in_symbol_ptr;
  num_rules = num_base_symbols + num_rules_defined;
  *end_symbol_ptr = 0x80000000 + num_rules;

  symbol_count_ptr = (U64 *)symbol_count;
  while (symbol_count_ptr < (U64 *)(symbol_count + num_rules))
    *symbol_count_ptr++ = 0;

  // parse the data to determine symbol_counts
  in_symbol_ptr = start_symbol_ptr;
  do {
    symbol = *in_symbol_ptr++;
    while ((S32)symbol >= 0) {
      symbol_count[symbol]++;
      symbol = *in_symbol_ptr++;
    }
  } while (in_symbol_ptr <= end_symbol_ptr);

  log_num_symbols = log2((double)num_in_symbols);
  log_num_symbols_plus_tokenization_cost = log_num_symbols + 1.4;

  order_0_entropy = 0.0;
  i1 = 0;
  do {
    if (symbol_count[i1]) {
      d_symbol_count = (double)symbol_count[i1];
      order_0_entropy -= d_symbol_count * log2((double)symbol_count[i1]);
    }
  } while (++i1 < num_base_symbols);

  if (num_rules_defined) {
    while (i1 < num_rules) {
      d_symbol_count = (double)symbol_count[i1];
      order_0_entropy -= d_symbol_count * log2(d_symbol_count);
    }
    d_symbol_count = (double)num_rules_defined;
    order_0_entropy -= d_symbol_count * log2(d_symbol_count);
  }
  order_0_entropy = (order_0_entropy / (double)num_in_symbols) + log_num_symbols;
  fprintf(stderr,"%u syms, dict. size %u, %.4f bits/sym, o0e %u bytes\n",(unsigned int)num_in_symbols,
      (unsigned int)num_rules_defined,order_0_entropy,(unsigned int)((double)num_in_symbols*order_0_entropy/8.0));

  if ((production_cost_paragraphs > 0.0) || ((production_cost_paragraphs < 0.0) && (UTF8_compliant || cap_encoded))) {
    // Allocate memory for for the suffix tree nodes
    string_nodes = (struct string_node *)malloc(sizeof(struct string_node) * 2 * symbol_count[0xa]);
    if (string_nodes == 0) {
      fprintf(stderr,"ERROR - Insufficient RAM to compress - unable to allocate %Iu bytes for the paragraph prefix tree\n",
        sizeof(struct string_node) * 2 * symbol_count[0xa]);
      exit(0);
    }

    production_cost = production_cost_paragraphs;
    if (production_cost < 0.0)
      production_cost = 75.0;
    in_symbol_ptr = start_symbol_ptr;
    next_string_node_num = 1;

    base_string_nodes_child_node_num[0xa * BASE_NODES_CHILD_ARRAY_SIZE] = 0;
    base_string_nodes_child_node_num[0xa * BASE_NODES_CHILD_ARRAY_SIZE + 1] = 0;

    fprintf(stderr,"Building paragraph suffix tree\n");
    old_time = 0;
    do {
      if (*in_symbol_ptr == 0xa) {
        if (*(in_symbol_ptr+1) != 0xa) {
          add_suffix(in_symbol_ptr);
          if (((in_symbol_ptr - start_symbol_ptr) & 0xF) == 0) {
            new_time = clock();
            if (new_time - old_time > 500) {
              old_time = new_time;
              fprintf(stderr,"%u/%u \r",
                  (unsigned int)(in_symbol_ptr-start_symbol_ptr),(unsigned int)(end_symbol_ptr-start_symbol_ptr));
            }
          }
        }
      }
      else if (*in_symbol_ptr == 0x80000000 + num_rules)
        break; // exit loop on EOF
      in_symbol_ptr++;
    } while (1);

    fprintf(stderr,"Deduplicating paragraphs\n");
    in_symbol_ptr = start_symbol_ptr;
    this_symbol = BLANK;
    found_new_rule = 0;
    old_time = 0;
    while (1) {
      this_symbol = *in_symbol_ptr;
      U32 * next_symbol_ptr = in_symbol_ptr;
      while (*++next_symbol_ptr == BLANK);
      if (((this_symbol == 0xa) || ((S32)this_symbol >= (S32)num_base_symbols))
          && (*next_symbol_ptr != 0xa) && (*next_symbol_ptr < num_base_symbols)) {
        find_paragraph(in_symbol_ptr);
        if (found_new_rule) {
          substitute(in_symbol_ptr);
          new_time = clock();
          if (new_time - old_time > 500) {
            old_time = new_time;
            fprintf(stderr,"%u/%u: %u symbols \r",(unsigned int)(in_symbol_ptr-start_symbol_ptr),
                (unsigned int)(end_symbol_ptr-start_symbol_ptr),(unsigned int)num_in_symbols);
          }
        }
        else {
          in_symbol_ptr = next_symbol_ptr;
          while (*++in_symbol_ptr == BLANK);
        }
      }
      else
        if (*in_symbol_ptr == 0x80000000 + num_rules)
          break;
      in_symbol_ptr = next_symbol_ptr;
    }
    fprintf(stderr,"%u/%u: %u symbols \n",(unsigned int)(in_symbol_ptr-start_symbol_ptr),
        (unsigned int)(end_symbol_ptr-start_symbol_ptr),(unsigned int)num_in_symbols);
    in_symbol_ptr = start_symbol_ptr;
    U32 * move_symbol_ptr = in_symbol_ptr;
    while (in_symbol_ptr <= end_symbol_ptr) {
      if (*in_symbol_ptr != BLANK)
        *move_symbol_ptr++ = *in_symbol_ptr;
      in_symbol_ptr++;
    }
    end_symbol_ptr = move_symbol_ptr - 1;
    new_symbol_index = end_symbol_ptr - start_symbol_ptr;
    free(string_nodes);
  }

  if ((production_cost_words > 0.0) || ((production_cost_words < 0.0) && (UTF8_compliant || cap_encoded))) {
    // Allocate memory for for the suffix tree nodes
    string_nodes = (struct string_node *)malloc(sizeof(struct string_node) * 2 * symbol_count[0x20]);
    if (string_nodes == 0) {
      fprintf(stderr,"ERROR - Insufficient RAM to compress - unable to allocate %Iu bytes for the word prefix tree\n",
        sizeof(struct string_node) * 2 * symbol_count[0x20]);
      exit(0);
    }

    production_cost = production_cost_words;
    if (production_cost < 0.0)
      production_cost = 75.0;
    in_symbol_ptr = start_symbol_ptr;
    next_string_node_num = 1;
    num_paragraph_symbols = num_rules;

    base_node_ptr = (U64 *)base_string_nodes_child_node_num;
    while (base_node_ptr < (U64 *)&base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE]) {
      *base_node_ptr = 0;
      *(base_node_ptr + 1) = 0;
      base_node_ptr += 2;
    }

    fprintf(stderr,"Building word suffix tree\n");
    old_time = 0;
    do {
      if (*in_symbol_ptr == 0x20) {
        if ((*(in_symbol_ptr+1) != 0x20) && (*(in_symbol_ptr+1) < num_base_symbols)) {
          add_suffix(in_symbol_ptr);
          if (((in_symbol_ptr - start_symbol_ptr) & 0xF) == 0) {
            new_time = clock();
            if (new_time - old_time > 500) {
              old_time = new_time;
              fprintf(stderr,"%u/%u\r",
                  (unsigned int)(in_symbol_ptr-start_symbol_ptr),(unsigned int)(end_symbol_ptr-start_symbol_ptr));
            }
          }
          in_symbol_ptr++;
        }
      }
      else if (*in_symbol_ptr == 0x80000000 + num_rules)
        break; // exit loop on EOF
      in_symbol_ptr++;
    } while (1);

    fprintf(stderr,"Deduplicating words  \n");
    in_symbol_ptr = start_symbol_ptr;
    this_symbol = BLANK;
    found_new_rule = 0;
    old_time = 0;
    while (1) {
      this_symbol = *in_symbol_ptr;
      U32 * next_symbol_ptr = in_symbol_ptr;
      while (*++next_symbol_ptr == BLANK);
      if (((this_symbol == 0x20) || ((S32)this_symbol >= (S32)num_paragraph_symbols))
          && (*next_symbol_ptr != 0x20) && (*next_symbol_ptr < num_base_symbols)) {
        find_word(in_symbol_ptr);
        if (found_new_rule) {
          substitute(in_symbol_ptr);
          new_time = clock();
          if (new_time - old_time > 500) {
            old_time = new_time;
            fprintf(stderr,"%u/%u: %u symbols \r",(unsigned int)(in_symbol_ptr-start_symbol_ptr),
                (unsigned int)(end_symbol_ptr-start_symbol_ptr),(unsigned int)num_in_symbols);
          }
          while (*++in_symbol_ptr == BLANK);
        }
        else {
          in_symbol_ptr = next_symbol_ptr;
          while (*++in_symbol_ptr == BLANK);
        }
      }
      else {
        if (*in_symbol_ptr == 0x80000000 + num_rules)
          break;
        while (*++in_symbol_ptr == BLANK);
      }
    }
    fprintf(stderr,"%u/%u: %u symbols \n",(unsigned int)(in_symbol_ptr-start_symbol_ptr),
        (unsigned int)(end_symbol_ptr-start_symbol_ptr),(unsigned int)num_in_symbols);
    in_symbol_ptr = start_symbol_ptr;
    U32 * move_symbol_ptr = in_symbol_ptr;
    while (in_symbol_ptr <= end_symbol_ptr) {
      if (*in_symbol_ptr != BLANK)
        *move_symbol_ptr++ = *in_symbol_ptr;
      in_symbol_ptr++;
    }
    end_symbol_ptr = move_symbol_ptr - 1;
    new_symbol_index = end_symbol_ptr - start_symbol_ptr;
    free(string_nodes);
  }

  if (production_cost_chars > 0.0) {
    if (8 * (size_t)(end_symbol_ptr - start_symbol_ptr) < 5 * ((size_t)in_size + 1000)) {
      start_symbol_ptr--;
      U32 * old_start_symbol_ptr = start_symbol_ptr;
      start_symbol_ptr = (U32 *)realloc(start_symbol_ptr, 8 * (size_t)(end_symbol_ptr - start_symbol_ptr));
      end_symbol_ptr += start_symbol_ptr - old_start_symbol_ptr;
      start_symbol_ptr++;
    }

    // Allocate memory for for the suffix tree nodes
    run_string_nodes = (struct run_string_node *)malloc(sizeof(struct run_string_node) * 2 * (end_symbol_ptr - start_symbol_ptr));
    if (run_string_nodes == 0) {
      fprintf(stderr,"ERROR - Insufficient RAM to compress - unable to allocate %Iu bytes for the run prefix tree\n",
        sizeof(struct run_string_node) * 2 * (end_symbol_ptr - start_symbol_ptr));
      exit(0);
    }

    in_symbol_ptr = start_symbol_ptr;
    next_string_node_num = 1;
    production_cost = production_cost_chars;
    base_node_ptr = (U64 *)base_string_nodes_child_node_num;
    while (base_node_ptr < (U64 *)&base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE]) {
      *base_node_ptr = 0;
      *(base_node_ptr + 1) = 0;
      base_node_ptr += 2;
    }

    fprintf(stderr,"Building run length suffix tree 0 - %x \n",(unsigned int)num_rules-1);
    old_time = 0;
    U32 prior_rules = num_rules;
    do {
      if ((S32)*in_symbol_ptr >= 0) {
        if (*in_symbol_ptr == *(in_symbol_ptr+1)) {
          add_run_suffix(in_symbol_ptr);
          if (((in_symbol_ptr - start_symbol_ptr) & 0xF) == 0) {
            new_time = clock();
            if (new_time - old_time > 500) {
              old_time = new_time;
              fprintf(stderr,"%u/%u\r",
                 (unsigned int)(in_symbol_ptr-start_symbol_ptr),(unsigned int)(end_symbol_ptr-start_symbol_ptr));
            }
          }
        }
      }
      else if (*in_symbol_ptr == 0x80000000 + num_rules)
        break;
      in_symbol_ptr++;
    } while (1);

    fprintf(stderr,"Deduplicating runs  \n");
    U32 symbol;
    for (symbol = 0 ; symbol < prior_rules ; symbol++) {
      if (base_string_nodes_child_node_num[2 * symbol + (symbol & 1)])
        if (run_string_nodes[base_string_nodes_child_node_num[2 * symbol + (symbol & 1)]].found_overlap)
          if (2 * (U64)num_in_symbols * ((U64)run_string_nodes
                  [base_string_nodes_child_node_num[2 * symbol + (symbol & 1)]].no_overlap_instances - 1)
              > 5 * (U64)symbol_count[symbol] * (U64)symbol_count[symbol])
            substitute_runs(symbol);
    }

    log_num_symbols = log2((double)num_in_symbols);
    log_num_symbols_plus_tokenization_cost = log_num_symbols + 1.4;

    in_symbol_ptr = start_symbol_ptr;
    U32 * move_symbol_ptr = in_symbol_ptr;
    while (in_symbol_ptr <= end_symbol_ptr) {
      if (*in_symbol_ptr != BLANK)
        *move_symbol_ptr++ = *in_symbol_ptr;
      in_symbol_ptr++;
    }
    end_symbol_ptr = move_symbol_ptr - 1;
    new_symbol_index = end_symbol_ptr - start_symbol_ptr;
    free(run_string_nodes);
  }

  if (production_cost_chars > 0.0) {
    if (8 * (size_t)(end_symbol_ptr - start_symbol_ptr) < 5 * ((size_t)in_size + 1000)) {
      start_symbol_ptr--;
      U32 * old_start_symbol_ptr = start_symbol_ptr;
      start_symbol_ptr = (U32 *)realloc(start_symbol_ptr, 8 * (size_t)(end_symbol_ptr - start_symbol_ptr));
      end_symbol_ptr += start_symbol_ptr - old_start_symbol_ptr;
      start_symbol_ptr++;
    }

    // Allocate memory for for the suffix tree nodes
    string_nodes = (struct string_node *)malloc(sizeof(struct string_node) * 2 * (end_symbol_ptr - start_symbol_ptr));
    if (string_nodes == 0) {
      fprintf(stderr,"ERROR - Insufficient RAM to compress - unable to allocate %Iu bytes for the prefix tree\n",
        sizeof(struct string_node) * 2 * (end_symbol_ptr - start_symbol_ptr));
      exit(0);
    }

    in_symbol_ptr = start_symbol_ptr;
    next_string_node_num = 1;
    production_cost = production_cost_chars;
    base_node_ptr = (U64 *)base_string_nodes_child_node_num;
    while (base_node_ptr < (U64 *)&base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE]) {
      *base_node_ptr = 0;
      *(base_node_ptr + 1) = 0;
      base_node_ptr += 2;
    }

    fprintf(stderr,"Building suffix tree 0 - %x \n",(unsigned int)num_rules-1);
    old_time = 0;
    do {
      if ((S32)*in_symbol_ptr >= 0) {
        add_suffix(in_symbol_ptr);
        if (((in_symbol_ptr - start_symbol_ptr) & 0xF) == 0) {
          new_time = clock();
          if (new_time - old_time > 500) {
            old_time = new_time;
            fprintf(stderr,"%u/%u\r",
                (unsigned int)(in_symbol_ptr-start_symbol_ptr),(unsigned int)(end_symbol_ptr-start_symbol_ptr));
          }
        }
      }
      else if (*in_symbol_ptr == 0x80000000 + num_rules)
        break;
      in_symbol_ptr++;
    } while (1);

    fprintf(stderr,"Deduplicating strings \n");
    in_symbol_ptr = start_symbol_ptr;
    found_new_rule = 0;
    free_nodes_list_length = 0;
    old_time = 0;
    while (1) {
      if ((*in_symbol_ptr & 0x80000000) == 0) {
        find_best_string(in_symbol_ptr,1);
        if (found_new_rule) {
          U16 initial_best_length = best_length;
          U16 saved_best_length = initial_best_length;
          double initial_best_score = best_score;
          struct string_node * initial_best_node_ptr = best_node_ptr;
          U32 * tisp = in_symbol_ptr;
          U32 k;
          for (k = 1 ; k < initial_best_length ; k++) {
            while (*++tisp == BLANK);
            find_best_string(tisp,0);
            if (found_new_rule) {
              if (best_score > initial_best_score) {
                if ((k == 1) || (string_score[k] <= 0.0))
                  goto skip_sym;
                U32 k1 = k;
                if (k > 2) {
                  U32 k2 = k - 1;
                  do {
                    if ((string_score[k2] > string_score[k]) && (string_node_ptr[k2] != string_node_ptr[k2+1]))
                      k1 = k2;
                  } while (--k2 >= 2);
                }
                if (string_score[k1] < 10.0)
                  goto skip_sym;
                initial_best_length = k1;
                initial_best_score = best_score;
                initial_best_node_ptr = string_node_ptr[k1];
              }
            }
          }
          best_length = initial_best_length;
          best_node_ptr = initial_best_node_ptr;
          substitute_and_update_tree(in_symbol_ptr);
          new_time = clock();
          if (new_time - old_time > 500) {
            old_time = new_time;
            fprintf(stderr,"%u/%u: %u symbols \r",(unsigned int)(in_symbol_ptr-start_symbol_ptr),
                (unsigned int)(end_symbol_ptr-start_symbol_ptr),(unsigned int)num_in_symbols);
          }
        }
        else
          while (*++in_symbol_ptr == BLANK);
      }
      else {
        if (*in_symbol_ptr == 0x80000000 + num_rules)
          break;
skip_sym:
        while (*++in_symbol_ptr == BLANK);
      }
    }
    fprintf(stderr,"%u/%u: %u symbols \n",(unsigned int)(in_symbol_ptr-start_symbol_ptr),
        (unsigned int)(end_symbol_ptr-start_symbol_ptr),(unsigned int)num_in_symbols);
    free(string_nodes);
  }

write_file:
  sprintf((char *)out_file_name,"%s",argv[arg_num]);
  if ((fd_out = fopen((char *)out_file_name,"wb+")) == NULL) {
    fprintf(stderr,"ERROR - unable to open output file '%s'\n",out_file_name);
    exit(0);
  }

  char_buffer = (U8 *)(start_symbol_ptr - 1);
  in_char_ptr = char_buffer;
  *in_char_ptr++ = cap_encoded + (delta_gap * 2);
  in_symbol_ptr = start_symbol_ptr;
  if (UTF8_compliant) {
    while (in_symbol_ptr != end_symbol_ptr) {
      while (*in_symbol_ptr == BLANK)
        in_symbol_ptr++;
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
      else if ((S32)symbol_value >= 0) {
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
      while (*in_symbol_ptr == BLANK)
        in_symbol_ptr++;
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
      else if ((S32)symbol_value >= 0) {
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
  fclose(fd_out);
  free(back_nodes);
  free(match_start_nodes);
  free(match_list);
  free(start_symbol_ptr-1);
  fprintf(stderr,"Created %u rule grammar in %.3f seconds.\n",
      (unsigned int)num_rules-num_base_symbols,(float)(clock()-start_time)/CLOCKS_PER_SEC);
  return(0);
}
