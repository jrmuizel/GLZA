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
//       c specifies the character deduplication minimum score.  Must not be negative.
//       m specifies the approximate RAM usage / input file size ratio (default 6.5 for UTF-8 compliant
//       files, 10.5 for non UTF-8 compliant files, minimum is 5.0).

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <pthread.h>

const unsigned char INSERT_SYMBOL_CHAR = 0xFE;
const unsigned char DEFINE_SYMBOL_CHAR = 0xFF;
const unsigned int START_MY_SYMBOLS = 0x00080000;
const unsigned int MAX_WRITE_SIZE = 0x200000;
const unsigned int MAX_STRING_LENGTH = 40000;
const unsigned int BASE_NODES_CHILD_ARRAY_SIZE = 2;
const unsigned int BLANK = 0xFFFFFFFF;
const unsigned int EOF_SYMBOL = 0xFFFFFFFE;
const unsigned int FREE_NODES_LIST_SIZE = 0x10000;

static struct string_node {
  unsigned int symbol;
  unsigned int match_start_index;
  unsigned int sibling_node_num[2];
  unsigned int instances;
  unsigned int child_node_num;
  unsigned short int num_extra_symbols;
  unsigned char found_overlap;
} *string_nodes, *free_node_ptr, *node_ptr;

static struct run_string_node {
  unsigned int symbol;
  unsigned int match_start_index;
  unsigned int sibling_node_num[2];
  unsigned int instances;
  unsigned int no_overlap_instances;
  unsigned int child_node_num;
  unsigned short int num_extra_symbols;
  unsigned char found_overlap;
} *run_string_nodes, *run_free_node_ptr, *run_node_ptr;

static struct back_node {
  unsigned int symbol;
  unsigned int last_match_index;
  unsigned int sibling_node_num[2];
  unsigned int instances;
  unsigned int child_node_num;
  unsigned int next_back_node_num;
  unsigned int depth;
} *back_nodes;

static struct match_start_node {
  unsigned int match_index;
  unsigned int depth;
  unsigned int child_node_num1;
  unsigned int child_node_num2;
} *match_start_nodes;

unsigned int this_symbol, num_in_symbols, new_symbol_index, max_string_length, match_start_index;
unsigned int next_string_node_num, shifted_search_symbol, best_inst, i1;
unsigned int num_rules, num_rules_defined, num_base_symbols, num_paragraph_symbols;
unsigned int symbol_count[10000000], base_string_nodes_child_node_num[20000000];
unsigned int *symbol_ptr, *start_symbol_ptr, *end_symbol_ptr, *in_symbol_ptr, *out_symbol_ptr;
unsigned int *match_list, *best_score_last_match_ptr, *prior_node_num_ptr, *node_last_match_ptr;
unsigned int match_list_length, node_list_length, next_match_index_index, sorted_match_index;
unsigned int match_start_indexes[30000000];
unsigned int node_list[40001], first_back_node_of_depth[40001], max_back_node_depth;
unsigned int free_nodes_list_length, free_nodes_list[0x10000];
unsigned short int node_ptrs_num, best_length;
unsigned char made_new_rule, found_overlap;
unsigned char *char_buffer, *in_char_ptr, *out_char_ptr, *end_char_ptr;
double d_num_symbols, d_num_symbols_inv, cutoff_score, log_num_symbols;
double d_num_symbols_in_string_inv[40001];
double log_symbol_count_minus_log_num_symbols[10000000];
struct string_node *first_single_instance_node_ptr, *end_match_node_ptr, *prior_node_ptr, *best_node_ptr;


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


static inline void add_suffix(unsigned int * first_symbol_ptr)
{
  struct string_node *child_ptr;
  unsigned int match_start_index = first_symbol_ptr - start_symbol_ptr;
  unsigned int * match_max_ptr = first_symbol_ptr + MAX_STRING_LENGTH;
  unsigned int * in_symbol_ptr = first_symbol_ptr;
  unsigned int this_symbol = *in_symbol_ptr++;
  unsigned int search_symbol = *in_symbol_ptr;
  unsigned int num_extra_symbols;

  prior_node_num_ptr = &base_string_nodes_child_node_num[this_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)];
  if (*prior_node_num_ptr == 0) { // first base node child, so create a child
    child_ptr = &string_nodes[next_string_node_num];
    write_node_ptr_data(child_ptr, search_symbol, match_start_index, 0, 0, 1, 0, 0, 0);
    *prior_node_num_ptr = next_string_node_num++;
    return;
  }
  child_ptr = &string_nodes[*prior_node_num_ptr];
  if (search_symbol != child_ptr->symbol) { // follow siblings until match found or end of siblings found
    shifted_search_symbol = search_symbol;
    do {
      shifted_search_symbol >>= 1;
      prior_node_num_ptr = &child_ptr->sibling_node_num[shifted_search_symbol & 1];
      if (*prior_node_num_ptr == 0) {
        child_ptr = &string_nodes[next_string_node_num];
        write_node_ptr_data(child_ptr, search_symbol, match_start_index, 0, 0, 1, 0, 0, 0);
        *prior_node_num_ptr = next_string_node_num++;
        return;
      }
      child_ptr = &string_nodes[*prior_node_num_ptr];
    } while (search_symbol != child_ptr->symbol);
  }

  // found a matching sibling
  while (child_ptr->child_node_num) {
    // matching sibling with child so check length of match
    num_extra_symbols = child_ptr->num_extra_symbols;
    unsigned int * child_symbol_ptr = in_symbol_ptr - match_start_index + child_ptr->match_start_index;
    if (num_extra_symbols) {
      unsigned int length = 1;
      do {
        if (*(child_symbol_ptr + length) != *(in_symbol_ptr + length)) { /* insert node in branch */
          child_ptr->num_extra_symbols = length - 1;
          unsigned int move_child_num = child_ptr->child_node_num;
          child_ptr->child_node_num = next_string_node_num;
          node_ptr = &string_nodes[next_string_node_num++];
          unsigned char overlap;
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
    prior_node_num_ptr = &child_ptr->child_node_num;
    child_ptr = &string_nodes[*prior_node_num_ptr];
    if (search_symbol != child_ptr->symbol) { // follow siblings until match found or end of siblings found
      shifted_search_symbol = search_symbol;
      do {
        prior_node_num_ptr = &child_ptr->sibling_node_num[shifted_search_symbol & 1];
        if (*prior_node_num_ptr == 0) {
          child_ptr = &string_nodes[next_string_node_num];
          write_node_ptr_data(child_ptr, search_symbol, match_start_index, 0, 0, 1, 0, 0, 0);
          *prior_node_num_ptr = next_string_node_num++;
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
  unsigned int length = 1;
  unsigned int * child_symbol_ptr = in_symbol_ptr - match_start_index + child_ptr->match_start_index;
  while (*(child_symbol_ptr + length) == *(in_symbol_ptr + length)) {
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


static inline void add_run_suffix(unsigned int * first_symbol_ptr)
{
  struct run_string_node *child_ptr;
  unsigned int match_start_index = first_symbol_ptr - start_symbol_ptr;
  unsigned int * match_max_ptr = first_symbol_ptr + MAX_STRING_LENGTH;
  unsigned int * in_symbol_ptr = first_symbol_ptr;
  unsigned int this_symbol = *in_symbol_ptr++;
  unsigned int search_symbol = *in_symbol_ptr;
  unsigned int num_extra_symbols;

  prior_node_num_ptr = &base_string_nodes_child_node_num[this_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)];
  if (*prior_node_num_ptr == 0) { // first base node child, so create a child
    child_ptr = &run_string_nodes[next_string_node_num];
    write_run_node_ptr_data(child_ptr, search_symbol, match_start_index, 0, 0, 1, 1, 0, 0, 0);
    *prior_node_num_ptr = next_string_node_num++;
    return;
  }
  child_ptr = &run_string_nodes[*prior_node_num_ptr];
  if (search_symbol != child_ptr->symbol) { // follow siblings until match found or end of siblings found
    shifted_search_symbol = search_symbol;
    do {
      shifted_search_symbol >>= 1;
      prior_node_num_ptr = &child_ptr->sibling_node_num[shifted_search_symbol & 1];
      if (*prior_node_num_ptr == 0) {
        child_ptr = &run_string_nodes[next_string_node_num];
        write_run_node_ptr_data(child_ptr, search_symbol, match_start_index, 0, 0, 1, 1, 0, 0, 0);
        *prior_node_num_ptr = next_string_node_num++;
        return;
      }
      child_ptr = &run_string_nodes[*prior_node_num_ptr];
    } while (search_symbol != child_ptr->symbol);
  }

  // found a matching sibling
  while (child_ptr->child_node_num) {
    // matching sibling with child so check length of match
    num_extra_symbols = child_ptr->num_extra_symbols;
    unsigned int * child_symbol_ptr = in_symbol_ptr - match_start_index + child_ptr->match_start_index;
    if (num_extra_symbols) {
      unsigned int length = 1;
      do {
        if (*(child_symbol_ptr + length) != *(in_symbol_ptr + length)) { /* insert node in branch */
          child_ptr->num_extra_symbols = length - 1;
          unsigned int move_child_num = child_ptr->child_node_num;
          child_ptr->child_node_num = next_string_node_num;
          run_node_ptr = &run_string_nodes[next_string_node_num++];
          unsigned char overlap;
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
          child_ptr = &run_string_nodes[next_string_node_num];
          write_run_node_ptr_data(child_ptr, search_symbol, match_start_index, 0, 0, 1, 1, 0, 0, 0);
          *prior_node_num_ptr = next_string_node_num++;
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
  unsigned int length = 1;
  unsigned int * child_symbol_ptr = in_symbol_ptr - match_start_index + child_ptr->match_start_index;
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


void get_string_starts(unsigned int node_num) {
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


void get_run_string_starts(unsigned int node_num) {
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


void sort_match_indexes(unsigned int node_num) {
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
  unsigned int * prior_node_addr_ptr = 0; \
  unsigned int sibling = 0; \
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
  unsigned int first_symbol, search_symbol; \
  first_symbol = *symbol_ptr; \
  get_symbol(search_symbol); \
  node_ptr = &string_nodes[base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)]]; \
  find_base_node_sibling(); \
  unsigned int search_length = suffix_length - 2; \
  node_ptr->instances -= best_inst - 1; \
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
      node_ptr->instances -= best_inst - 1; \
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
  unsigned int first_symbol, search_symbol; \
  first_symbol = *symbol_ptr; \
  get_symbol(search_symbol); \
  node_ptr = &string_nodes[base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)]]; \
  find_base_node_sibling(); \
  unsigned int search_length = suffix_length - 2; \
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
        for (i = 0 ; i < best_length - 1 ; i++) \
          while (*++symbol_ptr == BLANK); \
      } \
      while (*++symbol_ptr == BLANK); \
    } \
    else { \
      prior_node_num_ptr = &node_ptr->child_node_num; \
      unsigned int search_symbol = *symbol_ptr; \
      node_ptr = &string_nodes[node_ptr->child_node_num]; \
      if (symbol_ptr - start_symbol_ptr == match_start_indexes[next_match_index_index]) { \
        next_match_index_index--; \
        search_symbol = num_rules; \
        for (i = 0 ; i < best_length - 1 ; i++) { \
          while (*++symbol_ptr == BLANK); \
        } \
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
  unsigned int first_symbol = *symbol_ptr; \
  unsigned int search_symbol; \
  get_symbol(search_symbol); \
  if (symbol_ptr - start_symbol_ptr == match_start_indexes[next_match_index_index]) { \
    next_match_index_index--; \
    search_symbol = num_rules; \
    for (i = 0 ; i < best_length - 1 ; i++) \
      while (*++symbol_ptr == BLANK); \
  } \
  while (*++symbol_ptr == BLANK); \
  prior_node_num_ptr = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)]; \
  node_ptr = &string_nodes[*prior_node_num_ptr]; \
  find_base_node_sibling(); \
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
          for (i = 0 ; i < best_length - 1 ; i++) { \
            while (*++symbol_ptr == BLANK); \
          } \
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
          for (i = 0 ; i < best_length - 1 ; i++) \
            while (*++symbol_ptr == BLANK); \
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
  unsigned int first_symbol = *symbol_ptr; \
  shifted_search_symbol = search_symbol; \
  prior_node_num_ptr = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)]; \
  find_last_sibling(); \
  *prior_node_num_ptr = free_node_ptr - string_nodes; \
  write_node_ptr_data(free_node_ptr, search_symbol, new_symbol_index + best_length, 0, 0, 1, 0, 0, 0); \
}


#define score_paragraph() { \
  if (node_ptr->instances == 2) { \
    double profit_per_sub = log2(d_num_symbols_inv) - log_expected_match_ratio; \
    if (profit_per_sub >= cutoff_score) { \
      best_length = symbols_in_string; \
      best_inst = node_ptr->instances; \
      best_node_ptr = node_ptr; \
      made_new_rule = 1; \
    } \
  } \
  else { \
    double d_node_instances_m_1 = (double)(node_ptr->instances - 1); \
    double profit_per_sub = log2(d_node_instances_m_1 * d_num_symbols_inv) - log_expected_match_ratio; \
    if (profit_per_sub >= 1.4) { \
      if (d_node_instances_m_1 * profit_per_sub >= cutoff_score) { \
        best_length = symbols_in_string; \
        best_inst = node_ptr->instances; \
        best_node_ptr = node_ptr; \
        made_new_rule = 1; \
      } \
    } \
  } \
}


static inline void find_paragraph(unsigned int *first_symbol_ptr)
{
  double best_score = cutoff_score;
  unsigned int * in_symbol_ptr = first_symbol_ptr;
  unsigned int first_symbol = *in_symbol_ptr;
  unsigned int symbols_in_string = 2;
  double log_expected_match_ratio = log2((double)symbol_count[first_symbol]) - log_num_symbols;

  made_new_rule = 0;
  while (*++in_symbol_ptr == BLANK);
  if ((int)*in_symbol_ptr < 0)
    return;
  unsigned int search_symbol = *in_symbol_ptr;
  prior_node_num_ptr = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)];
  match_start_index = first_symbol_ptr - start_symbol_ptr;
  node_ptr = &string_nodes[*prior_node_num_ptr];

find_sibling_p:
  find_base_node_sibling();

found_sibling_p:
  if (node_ptr->instances == 1)
    return;
  log_expected_match_ratio += log2((double)symbol_count[search_symbol]) - log_num_symbols;
  unsigned int length = node_ptr->num_extra_symbols;
  unsigned int * next_symbol_ptr = in_symbol_ptr;
  while (*++next_symbol_ptr == BLANK);
  while (length) {
    if ((*next_symbol_ptr == 0xa) || (*next_symbol_ptr >= num_base_symbols)) {
      score_paragraph();
      return;
    }
    length--;
    in_symbol_ptr = next_symbol_ptr;
    while (*++next_symbol_ptr == BLANK);
    log_expected_match_ratio += log2((double)symbol_count[*in_symbol_ptr]) - log_num_symbols;
    symbols_in_string++;
  }
  if ((*next_symbol_ptr == 0xa) || (*next_symbol_ptr >= num_base_symbols)) {  // calculate this child's score
    score_paragraph();
    return;
  }
  search_symbol = *next_symbol_ptr;
  if ((int)search_symbol >= 0) {
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
    double profit_per_sub = log2(d_num_symbols_inv) - log_expected_match_ratio; \
    if (profit_per_sub >= cutoff_score) { \
      best_length = symbols_in_string; \
      best_inst = node_ptr->instances; \
      best_node_ptr = node_ptr; \
      made_new_rule = 1; \
    } \
  } \
  else { \
    double d_node_instances_m_1 = (double)(node_ptr->instances - 1); \
    double profit_per_sub = log2(d_node_instances_m_1 * d_num_symbols_inv) - log_expected_match_ratio; \
    if (profit_per_sub >= 1.4) { \
      if (d_node_instances_m_1 * profit_per_sub >= cutoff_score) { \
        best_length = symbols_in_string; \
        best_inst = node_ptr->instances; \
        best_node_ptr = node_ptr; \
        made_new_rule = 1; \
      } \
    } \
  } \
}


static inline void find_word(unsigned int *first_symbol_ptr)
{
  double best_score = cutoff_score;
  unsigned int * in_symbol_ptr = first_symbol_ptr;
  unsigned int first_symbol = *in_symbol_ptr;
  unsigned int symbols_in_string = 2;
  double log_expected_match_ratio = log2((double)symbol_count[first_symbol]) - log_num_symbols;

  made_new_rule = 0;
  while (*++in_symbol_ptr == BLANK);
  if ((int)*in_symbol_ptr < 0)
    return;
  unsigned int search_symbol = *in_symbol_ptr;
  prior_node_num_ptr = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)];
  match_start_index = first_symbol_ptr - start_symbol_ptr;
  node_ptr = &string_nodes[*prior_node_num_ptr];

find_sibling_w:
  find_base_node_sibling();

found_sibling_w:
  if (node_ptr->instances == 1)
    return;
  log_expected_match_ratio += log2((double)symbol_count[search_symbol]) - log_num_symbols;
  unsigned int length = node_ptr->num_extra_symbols;
  unsigned int * next_symbol_ptr = in_symbol_ptr;
  while (*++next_symbol_ptr == BLANK);
  while (length) {
    if ((*next_symbol_ptr == 0x20) || (*next_symbol_ptr >= num_base_symbols)) {
      score_word();
      return;
    }
    length--;
    in_symbol_ptr = next_symbol_ptr;
    while (*++next_symbol_ptr == BLANK);
    log_expected_match_ratio += log2((double)symbol_count[*in_symbol_ptr]) - log_num_symbols;
    symbols_in_string++;
  }
  if ((*next_symbol_ptr == 0x20) || (*next_symbol_ptr >= num_base_symbols)) {  // calculate this child's score
    score_word();
    return;
  }
  search_symbol = *next_symbol_ptr;
  if ((int)search_symbol >= 0) {
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


static inline void find_best_string(unsigned int *first_symbol_ptr)
{
  double best_score = 1.5;
  unsigned int * in_symbol_ptr = first_symbol_ptr;
  unsigned int first_symbol = *in_symbol_ptr;
  unsigned int symbols_in_string = 2;
  double log_expected_match_ratio = log2((double)symbol_count[first_symbol]) - log_num_symbols;

  best_length = 0;
  made_new_rule = 0;
  while (*++in_symbol_ptr == BLANK);
  if ((int)*in_symbol_ptr < 0)
    return;
  unsigned int search_symbol = *in_symbol_ptr;
  prior_node_num_ptr = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)];
  match_start_index = first_symbol_ptr - start_symbol_ptr;
  node_ptr = &string_nodes[*prior_node_num_ptr];

find_sibling:
  find_base_node_sibling();

found_sibling:
  if (node_ptr->instances == 1)
    goto check_best;
  log_expected_match_ratio += log2((double)symbol_count[search_symbol]) - log_num_symbols;
  unsigned int length = node_ptr->num_extra_symbols;
  symbols_in_string += length;
  while (length) {
    length--;
    while (*++in_symbol_ptr == BLANK);
    log_expected_match_ratio += log2((double)symbol_count[*in_symbol_ptr]) - log_num_symbols;
  }

  if (node_ptr->found_overlap == 0) {  // calculate this child's score
    if (node_ptr->instances == 2) {
      double profit_per_sub = log2(d_num_symbols_inv) - log_expected_match_ratio;
      if (profit_per_sub >= cutoff_score) {
        double d_score = (profit_per_sub - 1.4) * d_num_symbols_in_string_inv[symbols_in_string];
        if (d_score > best_score) {
          best_score = d_score;
          best_length = symbols_in_string;
          best_inst = node_ptr->instances;
          best_node_ptr = node_ptr;
        }
      }
    }
    else {
      double d_node_instances_m_1 = (double)(node_ptr->instances - 1);
      double profit_per_sub = log2(d_node_instances_m_1 * d_num_symbols_inv) - log_expected_match_ratio;
      double profit_margin = profit_per_sub - 1.4;
      if (profit_margin >= 0.0) {
        if (d_node_instances_m_1 * profit_per_sub >= cutoff_score) {
          double d_score = profit_margin * d_num_symbols_in_string_inv[symbols_in_string];
          if (d_score > best_score) {
            best_score = d_score;
            best_length = symbols_in_string;
            best_inst = node_ptr->instances;
            best_node_ptr = node_ptr;
          }
        }
      }
    }
  }
  while (*++in_symbol_ptr == BLANK);
  search_symbol = *in_symbol_ptr;
  if ((int)search_symbol >= 0) {
    node_ptr = &string_nodes[node_ptr->child_node_num];
    symbols_in_string++;
    if (search_symbol == node_ptr->symbol)
      goto found_sibling;
    if (node_ptr->sibling_node_num[search_symbol & 1]) {
      node_ptr = &string_nodes[node_ptr->sibling_node_num[search_symbol & 1]];
      goto find_sibling;
    }
  }

check_best:
  if (best_length)
    made_new_rule = 1;
  return;
}


static inline void substitute(unsigned int * first_symbol_ptr)
{
  unsigned int search_symbol, end_match_child_num, num_extra_symbols, first_symbol;
  unsigned char end_match_found_overlap;
  unsigned int * string_ptr = first_symbol_ptr;
  struct string_node * parent_node_ptr;

  match_list_length = 0;
  get_string_starts(best_node_ptr->child_node_num);

  /* decrement instances for substituted string */
  unsigned int sym_num = 0;
  symbol_ptr = start_symbol_ptr + match_list[0];
  first_symbol = *symbol_ptr;
  get_symbol(search_symbol);
  *++end_symbol_ptr = first_symbol;
  *++end_symbol_ptr = search_symbol;
  symbol_count[first_symbol] -= best_inst - 1;
  symbol_count[search_symbol] -= best_inst - 1;
  prior_node_num_ptr = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)];
  node_ptr = &string_nodes[*prior_node_num_ptr];
  find_base_node_sibling();
  node_ptr->instances -= best_inst - 1;
  unsigned int match_start_index = end_symbol_ptr - 1 - start_symbol_ptr;
  node_ptr->match_start_index = match_start_index;
  num_extra_symbols = node_ptr->num_extra_symbols;

  unsigned short int length = 2;

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
      node_ptr->instances -= best_inst - 1;
      node_ptr->match_start_index = match_start_index;
      num_extra_symbols = node_ptr->num_extra_symbols;
    }
    else {
      num_extra_symbols--;
      get_symbol(search_symbol);
    }
    symbol_count[search_symbol] -= best_inst - 1;
    *++end_symbol_ptr = search_symbol;
  }
  *++end_symbol_ptr = 0x80000001 + num_rules;
  symbol_count[num_rules] = best_inst;

  /* add prefixes starting with the rule for the match, move match child to rule child */
  unsigned int add_node_num = node_ptr->child_node_num;
  unsigned int next_add_node_num;
  unsigned int * prior_node_num_ptr;
  if (num_extra_symbols == 0) {
    base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE] = string_nodes[add_node_num].sibling_node_num[0];
    base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE + 1]
        = string_nodes[add_node_num].sibling_node_num[1];
    prior_node_num_ptr
        = &base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE + (string_nodes[add_node_num].symbol & 1)];
    next_add_node_num = *prior_node_num_ptr;
    *prior_node_num_ptr = add_node_num;
    unsigned char symbol_shift = 0;
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
        string_nodes[add_node_num].sibling_node_num[0], string_nodes[add_node_num].sibling_node_num[1], best_inst,
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
  num_in_symbols -= (best_inst - 1) * (best_length - 1) - 2;
  new_symbol_index += best_length + 1;
  d_num_symbols = (double)num_in_symbols;
  d_num_symbols_inv = 1.0 / d_num_symbols;
  log_num_symbols = log2(d_num_symbols);

  while (best_inst) {
    unsigned int * suffix_start_ptr = start_symbol_ptr + match_list[--best_inst];
    *suffix_start_ptr = num_rules;
    unsigned int i;
    for (i = 1 ; i < best_length ; i++) {
      while (*(suffix_start_ptr + i) == BLANK)
        suffix_start_ptr++;
      *(suffix_start_ptr + i) = BLANK;
    }
  }
  num_rules++;
}


static inline void substitute_runs(unsigned int run_symbol)
{
  match_list_length = 0;
  get_run_string_starts(base_string_nodes_child_node_num[2 * run_symbol + (run_symbol & 1)]);

  unsigned int match_index_bits = 1;
  unsigned int temp_num_in_symbols = new_symbol_index;
  while (temp_num_in_symbols >>= 1)
    match_index_bits++;
  match_start_nodes[0].match_index = match_list[0];
  match_start_nodes[0].child_node_num1 = 0;
  match_start_nodes[0].child_node_num2 = 0;
  unsigned int match_num = 1;
  unsigned int match_start_node_num;

  while (match_num < match_list_length) {
    unsigned int match_index = match_list[match_num];
    unsigned int saved_match_index;
    unsigned int node_bit = match_index_bits - 1;
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
  unsigned int longest_match = 0;
  unsigned int second_longest_match = 0;
  int match_length = 2;
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
  unsigned char max_power_2_reduction = 0;
  unsigned char temp_power_reduction;
  while (longest_match >>= 1)
    max_power_2_reduction++;
  num_in_symbols += (best_length + 1) * max_power_2_reduction;
  for (temp_power_reduction = 0 ; temp_power_reduction < max_power_2_reduction ; temp_power_reduction++)
    symbol_count[num_rules + temp_power_reduction] = 0;

  for (match_num = 1 ; match_num <= sorted_match_index ; match_num++) {
    if (match_start_indexes[match_num] == match_start_indexes[match_num - 1] + 1)
      match_length++;
    else {
      unsigned char power_reduction = 0;
      unsigned int temp_match_length = match_length;
      while (temp_match_length >>= 1)
        power_reduction++;
      if (power_reduction > max_power_2_reduction)
        power_reduction = max_power_2_reduction;
      unsigned int * write_ptr = start_symbol_ptr + match_start_indexes[match_num - 1] - match_length + 2;
      unsigned int * end_write_ptr = write_ptr + match_length;
      temp_power_reduction = power_reduction;
      while (temp_power_reduction) {
        while (match_length >= (1 << temp_power_reduction)) {
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


static inline void substitute_and_update_tree(unsigned int * first_symbol_ptr)
{
  unsigned int search_symbol, end_match_child_num, len, num_extra_symbols;
  unsigned int saved_match_start_index, first_symbol, back_node_num;
  unsigned int * string_ptr = first_symbol_ptr;
  unsigned char end_match_found_overlap;

  match_list_length = 0;
  get_string_starts(best_node_ptr->child_node_num);

  unsigned int back_node_index = match_list[0];
  while (*(start_symbol_ptr + --back_node_index) == BLANK);

  /* build back node tree */
  initialize_back_node_data(1, *(start_symbol_ptr + back_node_index), back_node_index, 1);
  unsigned int num_back_nodes = 2;
  max_back_node_depth = 1;
  first_back_node_of_depth[1] = 0;
  unsigned int match_num = 1;
  do {
    unsigned int * search_symbol_ptr = start_symbol_ptr + match_list[match_num];
    while (*--search_symbol_ptr == BLANK);
    search_symbol = *search_symbol_ptr;
    unsigned int tree_node = 1;
    unsigned int back_node_depth = 1;
    while (1) {
      unsigned int shifted_search_symbol = search_symbol;
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

  unsigned int match_index_bits = 1;
  unsigned int temp_num_in_symbols = new_symbol_index;
  while (temp_num_in_symbols >>= 1)
    match_index_bits++;

  back_node_num = 0;
  while (back_nodes[++back_node_num].instances != 1);
  match_start_nodes[0].match_index = back_nodes[back_node_num].last_match_index;
  unsigned int back_depth;
  for (back_depth = 0 ; back_depth < back_nodes[back_node_num].depth ; back_depth++)
    while (*(start_symbol_ptr + ++match_start_nodes[0].match_index) == BLANK);
  match_start_nodes[0].depth = back_nodes[back_node_num].depth;
  match_start_nodes[0].child_node_num1 = 0;
  match_start_nodes[0].child_node_num2 = 0;

  /* sort match indexes */
  unsigned int num_singles = 1;
  unsigned int match_start_node_num;
  while (++back_node_num < num_back_nodes) {
    if (back_nodes[back_node_num].instances == 1) {
      unsigned int depth = back_nodes[back_node_num].depth;
      unsigned int match_index = back_nodes[back_node_num].last_match_index;
      unsigned int i;
      for (i = 0 ; i < depth ; i++)
        while (*(start_symbol_ptr + ++match_index) == BLANK);

      unsigned int saved_match_index, saved_depth;
      unsigned int node_bit = match_index_bits - 1;
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

  unsigned int * end_suffix_symbol_ptr;
  unsigned int i;
  unsigned int i2 = 0;
  unsigned int match_start_node_num_array[32];
  unsigned char match_start_node_num_array_child_num[32];
  unsigned char depth = 0;
  match_start_node_num = 0;
  find_last_start_match_node();

  /* remove single instance back nodes via match start nodes, save indexes */
  while (1) {
    unsigned int check_depth = match_start_nodes[match_start_node_num].depth;
    match_start_index = match_start_nodes[match_start_node_num].match_index;
    match_start_indexes[++i2] = match_start_index;
    unsigned int * start_string_ptr = start_symbol_ptr + match_start_index;
    for (i = check_depth - 1 ; i != 0 ; i--)
      while (*--start_string_ptr == BLANK);

check_prior_start:
    while (1) {
      unsigned int * search_symbol_ptr = start_string_ptr;
      while (*--start_string_ptr == BLANK);
      symbol_ptr = start_string_ptr;
      unsigned int first_symbol = *symbol_ptr;
      if (first_symbol & 0x80000000)
        goto get_next_single;

      symbol_ptr = search_symbol_ptr;
      search_symbol = *symbol_ptr;
      prior_node_num_ptr = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)];
      node_ptr = &string_nodes[*prior_node_num_ptr];
      find_base_node_sibling();

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
        while (num_extra_symbols) {
          num_extra_symbols--;
          while (*++symbol_ptr == BLANK);
        }
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
          unsigned int new_string_node_num;
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
          while (num_extra_symbols) {
            num_extra_symbols--;
            while (*++symbol_ptr == BLANK);
          }
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
        while (num_extra_symbols) {
          num_extra_symbols--;
          while (*++symbol_ptr == BLANK);
        }
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
  unsigned int * end_match_symbol_ptr;
  unsigned int back_node_depth;
  unsigned int sum_inst = 0;
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
      unsigned char found_first_free_node = 0;
      if (back_node_depth >= 2) {
        find_base_node_sibling();
        num_extra_symbols = node_ptr->num_extra_symbols;
        unsigned int num_symbols = 2;
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
        unsigned int before_match_node_num = node_ptr - string_nodes;
        unsigned int next_child_node_num;

        if (num_extra_symbols >= best_length)
          node_ptr->num_extra_symbols -= best_length - 1;
        else {
          if (num_extra_symbols) {
            unsigned int new_string_node_num;
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
        find_base_node_sibling();
        node_ptr->instances -= back_nodes[back_node_num].instances;
        num_extra_symbols = node_ptr->num_extra_symbols;
        unsigned int next_child_node_num = node_ptr->child_node_num;
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
  match_start_index = match_start_indexes[best_inst];
  unsigned int * suffix_start_ptr = start_symbol_ptr + match_start_index;
  unsigned int suffix_length = best_length;
  unsigned int suffix_index = 1;
  end_match_symbol_ptr = suffix_start_ptr;
  for (i = 0 ; i < best_length ; i++)
    while (*++end_match_symbol_ptr == BLANK);
 
  unsigned int saved_num_extra_symbols;
  while (suffix_index < best_length - 1) {
    while (*++suffix_start_ptr == BLANK);
    suffix_length--;
    find_end_match_node_ptr_wd(suffix_start_ptr,suffix_length);
    if (first_single_instance_node_ptr) {
      first_single_instance_node_ptr->match_start_index = new_symbol_index + suffix_index + 1;
      first_single_instance_node_ptr->child_node_num = 0;
      first_single_instance_node_ptr->num_extra_symbols = 0;
    }
    else {
      next_match_index_index = best_inst - 1;
      remove_match_suffix();
      add_match_suffix(); /* suffix for new rule */

      /* remove non-first match non-first, non-last match symbol suffixes (except first match) */
      unsigned int * temp_suffix_start_ptr = start_symbol_ptr + match_start_indexes[best_inst];
      for (i = 0 ; i < suffix_index ; i++)
        while (*++temp_suffix_start_ptr == BLANK);
      unsigned int temp_suffix_length = best_length - suffix_index;
      find_end_match_node_ptr(temp_suffix_start_ptr,temp_suffix_length);
      unsigned int * save_end_match_symbol_ptr = end_match_symbol_ptr;
      saved_num_extra_symbols = num_extra_symbols;
      i2 = best_inst - 1;
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
  next_match_index_index = best_inst - 1;
  remove_match_suffix_1(suffix_start_ptr);
  add_match_suffix_1(suffix_start_ptr);

  /* remove non-first match last match symbol suffixes */
  i2 = best_inst - 1;
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
  unsigned int sym_num = 0;
  symbol_ptr = start_symbol_ptr + match_start_indexes[1];
  first_symbol = *symbol_ptr;
  get_symbol(search_symbol);
  *++end_symbol_ptr = first_symbol;
  *++end_symbol_ptr = search_symbol;
  symbol_count[first_symbol] -= best_inst - 1;
  symbol_count[search_symbol] -= best_inst - 1;
  prior_node_num_ptr = &base_string_nodes_child_node_num[first_symbol * BASE_NODES_CHILD_ARRAY_SIZE + (search_symbol & 1)];
  node_ptr = &string_nodes[*prior_node_num_ptr];
  find_base_node_sibling();
  node_ptr->instances -= best_inst - 1;
  unsigned int match_start_index = end_symbol_ptr - 1 - start_symbol_ptr;
  node_ptr->match_start_index = match_start_index;
  num_extra_symbols = node_ptr->num_extra_symbols;

  struct string_node * parent_node_ptr;
  unsigned short int length = 2;
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
      node_ptr->instances -= best_inst - 1;
      node_ptr->match_start_index = match_start_index;
      num_extra_symbols = node_ptr->num_extra_symbols;
    }
    else {
      num_extra_symbols--;
      get_symbol(search_symbol);
    }
    symbol_count[search_symbol] -= best_inst - 1;
    *++end_symbol_ptr = search_symbol;
  }
  *++end_symbol_ptr = 0x80000001 + num_rules;
  symbol_count[num_rules] = best_inst;

  /* add prefixes starting with the rule for the match, move match child to rule child */
  unsigned int add_node_num = node_ptr->child_node_num;
  unsigned int next_add_node_num;
  unsigned int * prior_node_num_ptr;
  base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE] = string_nodes[add_node_num].sibling_node_num[0];
  base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE + 1]
      = string_nodes[add_node_num].sibling_node_num[1];
  prior_node_num_ptr
      = &base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE + (string_nodes[add_node_num].symbol & 1)];
  next_add_node_num = *prior_node_num_ptr;
  *prior_node_num_ptr = add_node_num;
  unsigned char symbol_shift = 0;
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

  num_in_symbols -= (best_inst - 1) * (best_length - 1) - 2;
  new_symbol_index += best_length + 1;
  d_num_symbols = (double)num_in_symbols;
  d_num_symbols_inv = 1.0 / d_num_symbols;
  log_num_symbols = log2(d_num_symbols);

  while (best_inst) {
    suffix_start_ptr = start_symbol_ptr + match_start_indexes[best_inst--];
    *suffix_start_ptr = num_rules;
    unsigned int i;
    for (i = 1 ; i < best_length ; i++) {
      while (*(++suffix_start_ptr) == BLANK);
      *suffix_start_ptr = BLANK;
    }
  }
  num_rules++;
}


int main(int argc, char* argv[])
{
  FILE *fd_in, *fd_out;
  unsigned int in_size, arg_num, UTF8_value, max_UTF8_value, symbol;
  unsigned char UTF8_compliant, cap_encoded, this_char, delta_gap, out_char, out_file_name[50];
  unsigned char *write_ptr;
  double order_0_entropy, d_symbol_count, this_log_symbol_count_minus_log_num_symbols, log2_inv;
  double cutoff_score_paragraphs, cutoff_score_words, cutoff_score_chars;
  struct string_node *string_node_ptr;
  unsigned long long old_time, new_time, *base_node_ptr;

  unsigned long long start_time = (unsigned long long)clock();

  log2_inv = 1.0/log(2.0);
  for (i1 = 0 ; i1 < MAX_STRING_LENGTH ; i1++)
    d_num_symbols_in_string_inv[i1] = 1.0 / (double)i1;
  cutoff_score_paragraphs = -1.0;
  cutoff_score_words = -1.0;
  cutoff_score_chars = 8.0;
  arg_num = 1;
  while (*argv[arg_num] ==  '-') {
    if (*(argv[arg_num]+1) == 'p') {
      cutoff_score_paragraphs = (double)atof(argv[arg_num++]+2);
      if ((cutoff_score_paragraphs < 1.4) && (cutoff_score_paragraphs != 0.0)) {
        fprintf(stderr,"ERROR: positive -p values must be >= 1.4 or use 0.0 to disable\n");
        exit(0);
      }
    }
    else if (*(argv[arg_num]+1) == 'w') {
      cutoff_score_words = (double)atof(argv[arg_num++]+2);
      if ((cutoff_score_words < 1.4) && (cutoff_score_words != 0.0)) {
        fprintf(stderr,"ERROR: positive -w values must be >= 1.4 or use 0.0 to disable\n");
        exit(0);
      }
    }
    else if (*(argv[arg_num]+1) == 'c') {
      cutoff_score_chars = (double)atof(argv[arg_num++]+2);
      if ((cutoff_score_chars < 1.4) && (cutoff_score_chars != 0.0)) {
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

  back_nodes = (struct back_node *)malloc(sizeof(struct back_node) * 100000000);
  match_start_nodes = (struct match_start_node *)malloc(sizeof(struct match_start_node) * 30000000);
  match_list = (unsigned int *)malloc(sizeof(unsigned int) * 30000000);
  if ((back_nodes == 0) || (match_start_nodes == 0) || (match_list == 0)) {
    fprintf(stderr,"Malloc failed\n");
    exit(0);
  }

  start_symbol_ptr = (unsigned int *)malloc(5 * ((size_t)in_size + 1000));
  if (start_symbol_ptr == 0) {
    fprintf(stderr,"ERROR - Insufficient RAM to compress - unable to allocate %Iu bytes for input data\n",
        5 * ((size_t)in_size + 1000));
    exit(0);
  }

  *start_symbol_ptr++ = EOF_SYMBOL;
  in_symbol_ptr = start_symbol_ptr;

  char_buffer = (unsigned char *)start_symbol_ptr + 4 * in_size;
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

  fprintf(stderr,"capital encoded: %u, UTF-8 compliant %u\n",cap_encoded,UTF8_compliant);

  // parse the file to determine num_rules_defined and max_UTF8_value, convert characters to symbols
  num_rules_defined = 0;
  in_char_ptr = char_buffer + 1;

  if (UTF8_compliant) {
    num_base_symbols = START_MY_SYMBOLS;
    max_UTF8_value = 0;
    while (in_char_ptr != end_char_ptr) {
      this_char = *in_char_ptr++;
      if (this_char < 0x80)
        *in_symbol_ptr++ = (unsigned int)this_char;
      else if (this_char == INSERT_SYMBOL_CHAR) {
        *in_symbol_ptr++ = START_MY_SYMBOLS + 0x10000 * (unsigned int)*in_char_ptr
            + 0x100 * (unsigned int)*(in_char_ptr+1) + (unsigned int)*(in_char_ptr+2);
        in_char_ptr += 3;
      }
      else if (this_char == DEFINE_SYMBOL_CHAR) {
        *in_symbol_ptr++ = 0x80000000 + START_MY_SYMBOLS + 0x10000 * (unsigned int)*in_char_ptr
            + 0x100 * (unsigned int)*(in_char_ptr+1) + (unsigned int)*(in_char_ptr+2);
        in_char_ptr += 3;
        num_rules_defined++;
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
        *in_symbol_ptr++ = UTF8_value;
      }
    }
    fprintf(stderr,"Maximum unicode value 0x%x\n",max_UTF8_value);
  }
  else {
    num_base_symbols = 0x100;
    while (in_char_ptr != end_char_ptr) {
      this_char = *in_char_ptr++;
      if (this_char < INSERT_SYMBOL_CHAR)
        *in_symbol_ptr++ = (unsigned int)this_char;
      else {
        if (*in_char_ptr == DEFINE_SYMBOL_CHAR) {
          *in_symbol_ptr++ = (unsigned int)this_char;
          in_char_ptr++;
        }
        else {
          if (this_char == INSERT_SYMBOL_CHAR)
            *in_symbol_ptr++ = 0x100 + 0x10000 * (unsigned int)*in_char_ptr
                + 0x100 * (unsigned int)*(in_char_ptr+1) + (unsigned int)*(in_char_ptr+2);
          else {
            *in_symbol_ptr++ = 0x80000000 + 0x100 + 0x10000 * (unsigned int)*in_char_ptr
                + 0x100 * (unsigned int)*(in_char_ptr+1) + (unsigned int)*(in_char_ptr+2);
            num_rules_defined++;
          }
          in_char_ptr += 3;
        }
      }
    }
  }
  num_in_symbols = in_symbol_ptr - start_symbol_ptr;
  new_symbol_index = num_in_symbols; // IS nsi NEEDED? !! (same as nis?)
  fprintf(stderr,"Found %u symbols, %u defines\n",num_in_symbols,num_rules_defined);
  end_symbol_ptr = in_symbol_ptr;
  num_rules = num_base_symbols + num_rules_defined;
  *end_symbol_ptr = 0x80000000 + num_rules;

  unsigned long long * symbol_count_ptr = (unsigned long long *)symbol_count;
  while (symbol_count_ptr < (unsigned long long *)(symbol_count + num_rules))
    *symbol_count_ptr++ = 0;

  // parse the data to determine symbol_counts
  in_symbol_ptr = start_symbol_ptr;
  do {
    symbol = *in_symbol_ptr++;
    while ((int)symbol >= 0) {
      symbol_count[symbol]++;
      symbol = *in_symbol_ptr++;
    }
  } while (in_symbol_ptr <= end_symbol_ptr);

  d_num_symbols = (double)num_in_symbols;
  d_num_symbols_inv = 1.0 / d_num_symbols;

  order_0_entropy = 0.0;
  log_num_symbols = log2(d_num_symbols);
  i1 = 0;
  do {
    if (symbol_count[i1]) {
      d_symbol_count = (double)symbol_count[i1];
      this_log_symbol_count_minus_log_num_symbols = log2(d_symbol_count) - log_num_symbols;
      log_symbol_count_minus_log_num_symbols[i1] = this_log_symbol_count_minus_log_num_symbols;
      order_0_entropy -= d_symbol_count * this_log_symbol_count_minus_log_num_symbols;
    }
  } while (++i1 < num_base_symbols);

  if (num_rules_defined) {
    while (i1 < num_rules) {
      d_symbol_count = (double)symbol_count[i1];
      this_log_symbol_count_minus_log_num_symbols = log2(d_symbol_count) - log_num_symbols;
      log_symbol_count_minus_log_num_symbols[i1++] = this_log_symbol_count_minus_log_num_symbols;
      order_0_entropy -= d_symbol_count * this_log_symbol_count_minus_log_num_symbols;
    }
    d_symbol_count = (double)num_rules_defined;
    this_log_symbol_count_minus_log_num_symbols = log2(d_symbol_count) - log_num_symbols;
    order_0_entropy -= d_symbol_count * this_log_symbol_count_minus_log_num_symbols;
  }
  order_0_entropy *= d_num_symbols_inv;
  fprintf(stderr,"%u syms, dict. size %u, %.4f bits/sym, o0e %u bytes\n",
      num_in_symbols,num_rules_defined,order_0_entropy,(unsigned int)(d_num_symbols*order_0_entropy/8.0));

  if ((cutoff_score_paragraphs > 0.0) || ((cutoff_score_paragraphs < 0.0) && (UTF8_compliant || cap_encoded))) {
    // Allocate memory for for the suffix tree nodes
    string_nodes = (struct string_node *)malloc(sizeof(struct string_node) * 2 * symbol_count[0xa]);
    if (string_nodes == 0) {
      fprintf(stderr,"ERROR - Insufficient RAM to compress - unable to allocate %Iu bytes for the paragraph prefix tree\n",
        sizeof(struct string_node) * 2 * symbol_count[0xa]);
      exit(0);
    }

    cutoff_score = cutoff_score_paragraphs;
    if (cutoff_score < 0.0)
      cutoff_score = 75.0;
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
              fprintf(stderr,"%u/%u \r",in_symbol_ptr-start_symbol_ptr,end_symbol_ptr-start_symbol_ptr);
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
    made_new_rule = 0;
    old_time = 0;
    while (1) {
      this_symbol = *in_symbol_ptr;
      unsigned int * next_symbol_ptr = in_symbol_ptr;
      while (*++next_symbol_ptr == BLANK);
      if (((this_symbol == 0xa) || ((int)this_symbol >= (int)num_base_symbols))
          && (*next_symbol_ptr != 0xa) && (*next_symbol_ptr < num_base_symbols)) {
        find_paragraph(in_symbol_ptr);
        if (made_new_rule) {
          substitute(in_symbol_ptr);
          new_time = clock();
          if (new_time - old_time > 500) {
            old_time = new_time;
            fprintf(stderr,"%u/%u: %u symbols \r",in_symbol_ptr-start_symbol_ptr,end_symbol_ptr-start_symbol_ptr,num_in_symbols);
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
    fprintf(stderr,"%u/%u: %u symbols \n",in_symbol_ptr-start_symbol_ptr,end_symbol_ptr-start_symbol_ptr,num_in_symbols);
    in_symbol_ptr = start_symbol_ptr;
    unsigned int * move_symbol_ptr = in_symbol_ptr;
    while (in_symbol_ptr <= end_symbol_ptr) {
      if (*in_symbol_ptr != BLANK)
        *move_symbol_ptr++ = *in_symbol_ptr;
      in_symbol_ptr++;
    }
    end_symbol_ptr = move_symbol_ptr - 1;
    new_symbol_index = end_symbol_ptr - start_symbol_ptr;
    free(string_nodes);
  }



  if ((cutoff_score_words > 0.0) || ((cutoff_score_words < 0.0) && (UTF8_compliant || cap_encoded))) {
    // Allocate memory for for the suffix tree nodes
    string_nodes = (struct string_node *)malloc(sizeof(struct string_node) * 2 * symbol_count[0x20]);
    if (string_nodes == 0) {
      fprintf(stderr,"ERROR - Insufficient RAM to compress - unable to allocate %Iu bytes for the word prefix tree\n",
        sizeof(struct string_node) * 2 * symbol_count[0x20]);
      exit(0);
    }

    cutoff_score = cutoff_score_words;
    if (cutoff_score < 0.0)
      cutoff_score = 75.0;
    in_symbol_ptr = start_symbol_ptr;
    next_string_node_num = 1;
    num_paragraph_symbols = num_rules;

    base_node_ptr = (unsigned long long *)base_string_nodes_child_node_num;
    while (base_node_ptr < (unsigned long long *)&base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE]) {
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
              fprintf(stderr,"%u/%u\r",in_symbol_ptr-start_symbol_ptr,end_symbol_ptr-start_symbol_ptr);
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
    made_new_rule = 0;
    old_time = 0;
    while (1) {
      this_symbol = *in_symbol_ptr;
      unsigned int * next_symbol_ptr = in_symbol_ptr;
      while (*++next_symbol_ptr == BLANK);
      if (((this_symbol == 0x20) || ((int)this_symbol >= (int)num_paragraph_symbols))
          && (*next_symbol_ptr != 0x20) && (*next_symbol_ptr < num_base_symbols)) {
        find_word(in_symbol_ptr);
        if (made_new_rule) {
          substitute(in_symbol_ptr);
          new_time = clock();
          if (new_time - old_time > 500) {
            old_time = new_time;
            fprintf(stderr,"%u/%u: %u symbols \r",in_symbol_ptr-start_symbol_ptr,end_symbol_ptr-start_symbol_ptr,num_in_symbols);
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
    fprintf(stderr,"%u/%u: %u symbols \n",in_symbol_ptr-start_symbol_ptr,end_symbol_ptr-start_symbol_ptr,num_in_symbols);
    in_symbol_ptr = start_symbol_ptr;
    unsigned int * move_symbol_ptr = in_symbol_ptr;
    while (in_symbol_ptr <= end_symbol_ptr) {
      if (*in_symbol_ptr != BLANK)
        *move_symbol_ptr++ = *in_symbol_ptr;
      in_symbol_ptr++;
    }
    end_symbol_ptr = move_symbol_ptr - 1;
    new_symbol_index = end_symbol_ptr - start_symbol_ptr;
    free(string_nodes);
  }

  if (cutoff_score_chars > 0.0) {
    if (8 * (size_t)(end_symbol_ptr - start_symbol_ptr) < 5 * ((size_t)in_size + 1000)) {
      start_symbol_ptr--;
      unsigned int * old_start_symbol_ptr = start_symbol_ptr;
      start_symbol_ptr = (unsigned int *)realloc(start_symbol_ptr, 8 * (size_t)(end_symbol_ptr - start_symbol_ptr));
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
    cutoff_score = cutoff_score_chars;
    base_node_ptr = (unsigned long long *)base_string_nodes_child_node_num;
    while (base_node_ptr < (unsigned long long *)&base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE]) {
      *base_node_ptr = 0;
      *(base_node_ptr + 1) = 0;
      base_node_ptr += 2;
    }

    fprintf(stderr,"Building run length suffix tree 0 - %x \n",num_rules-1);
    old_time = 0;
    unsigned int prior_rules = num_rules;
    do {
      if ((int)*in_symbol_ptr >= 0) {
        if (*in_symbol_ptr == *(in_symbol_ptr+1)) {
          add_run_suffix(in_symbol_ptr);
          if (((in_symbol_ptr - start_symbol_ptr) & 0xF) == 0) {
            new_time = clock();
            if (new_time - old_time > 500) {
              old_time = new_time;
              fprintf(stderr,"%u/%u\r",in_symbol_ptr-start_symbol_ptr,end_symbol_ptr-start_symbol_ptr);
            }
          }
        }
      }
      else if (*in_symbol_ptr == 0x80000000 + num_rules)
        break;
      in_symbol_ptr++;
    } while (1);

    fprintf(stderr,"Deduplicating runs  \n");
    unsigned int symbol;
    for (symbol = 0 ; symbol < prior_rules ; symbol++) {
      if (base_string_nodes_child_node_num[2 * symbol + (symbol & 1)])
        if (run_string_nodes[base_string_nodes_child_node_num[2 * symbol + (symbol & 1)]].found_overlap)
          if (2 * (unsigned long long)num_in_symbols * ((unsigned long long)run_string_nodes
                  [base_string_nodes_child_node_num[2 * symbol + (symbol & 1)]].no_overlap_instances - 1)
              > 5 * (unsigned long long)symbol_count[symbol] * (unsigned long long)symbol_count[symbol])
            substitute_runs(symbol);
    }

    d_num_symbols = (double)num_in_symbols;
    d_num_symbols_inv = 1.0 / d_num_symbols;
    log_num_symbols = log2(d_num_symbols);

    in_symbol_ptr = start_symbol_ptr;
    unsigned int * move_symbol_ptr = in_symbol_ptr;
    while (in_symbol_ptr <= end_symbol_ptr) {
      if (*in_symbol_ptr != BLANK)
        *move_symbol_ptr++ = *in_symbol_ptr;
      in_symbol_ptr++;
    }
    end_symbol_ptr = move_symbol_ptr - 1;
    new_symbol_index = end_symbol_ptr - start_symbol_ptr;
    free(run_string_nodes);
  }

  if (cutoff_score_chars > 0.0) {
    if (8 * (size_t)(end_symbol_ptr - start_symbol_ptr) < 5 * ((size_t)in_size + 1000)) {
      start_symbol_ptr--;
      unsigned int * old_start_symbol_ptr = start_symbol_ptr;
      start_symbol_ptr = (unsigned int *)realloc(start_symbol_ptr, 8 * (size_t)(end_symbol_ptr - start_symbol_ptr));
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
    cutoff_score = cutoff_score_chars;
    base_node_ptr = (unsigned long long *)base_string_nodes_child_node_num;
    while (base_node_ptr < (unsigned long long *)&base_string_nodes_child_node_num[num_rules * BASE_NODES_CHILD_ARRAY_SIZE]) {
      *base_node_ptr = 0;
      *(base_node_ptr + 1) = 0;
      base_node_ptr += 2;
    }

    fprintf(stderr,"Building suffix tree 0 - %x \n",num_rules-1);
    old_time = 0;
    do {
      if ((int)*in_symbol_ptr >= 0) {
        add_suffix(in_symbol_ptr);
        if (((in_symbol_ptr - start_symbol_ptr) & 0xF) == 0) {
          new_time = clock();
          if (new_time - old_time > 500) {
            old_time = new_time;
            fprintf(stderr,"%u/%u\r",in_symbol_ptr-start_symbol_ptr,end_symbol_ptr-start_symbol_ptr);
          }
        }
      }
      else if (*in_symbol_ptr == 0x80000000 + num_rules)
        break;
      in_symbol_ptr++;
    } while (1);

    fprintf(stderr,"Deduplicating strings \n");
    in_symbol_ptr = start_symbol_ptr;
    made_new_rule = 0;
    free_nodes_list_length = 0;
    old_time = 0;
    while (1) {
      if ((*in_symbol_ptr & 0x80000000) == 0) {
        find_best_string(in_symbol_ptr);
        if (made_new_rule) {
          substitute_and_update_tree(in_symbol_ptr);
          new_time = clock();
          if (new_time - old_time > 500) {
            old_time = new_time;
            fprintf(stderr,"%u/%u: %u symbols \r",
                in_symbol_ptr-start_symbol_ptr,end_symbol_ptr-start_symbol_ptr,num_in_symbols);
          }
        }
        else
          while (*++in_symbol_ptr == BLANK);
      }
      else {
        if (*in_symbol_ptr == 0x80000000 + num_rules)
          break;
        while (*++in_symbol_ptr == BLANK);
      }
    }
    fprintf(stderr,"%u/%u: %u symbols \n",in_symbol_ptr-start_symbol_ptr,end_symbol_ptr-start_symbol_ptr,num_in_symbols);
    free(string_nodes);
  }

write_file:
  sprintf(out_file_name,"%s",argv[arg_num]);
  if ((fd_out = fopen(out_file_name,"wb+")) == NULL) {
    fprintf(stderr,"ERROR - unable to open output file '%s'\n",out_file_name);
    exit(0);
  }

  char_buffer = (unsigned char *)end_symbol_ptr;
  in_char_ptr = char_buffer;
  *in_char_ptr++ = cap_encoded + (delta_gap * 2);
  in_symbol_ptr = start_symbol_ptr;
  if (UTF8_compliant) {
    while (in_symbol_ptr != end_symbol_ptr) {
      while (*in_symbol_ptr == BLANK)
        in_symbol_ptr++;
      unsigned int symbol_value;
      symbol_value = *in_symbol_ptr++;
      if (symbol_value < 0x80)
        *in_char_ptr++ = (unsigned char)symbol_value;
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
        *in_char_ptr++ = (unsigned char)((symbol_value >> 16) & 0xFF);
        *in_char_ptr++ = (unsigned char)((symbol_value >> 8) & 0xFF);
        *in_char_ptr++ = (unsigned char)(symbol_value & 0xFF);
      }
      else {
        symbol_value -= 0x80000000 + START_MY_SYMBOLS;
        *in_char_ptr++ = DEFINE_SYMBOL_CHAR;
        *in_char_ptr++ = (unsigned char)((symbol_value >> 16) & 0xFF);
        *in_char_ptr++ = (unsigned char)((symbol_value >> 8) & 0xFF);
        *in_char_ptr++ = (unsigned char)(symbol_value & 0xFF);
      }
    }
  }
  else {
    while (in_symbol_ptr != end_symbol_ptr) {
      while (*in_symbol_ptr == BLANK)
        in_symbol_ptr++;
      unsigned int symbol_value;
      symbol_value = *in_symbol_ptr++;
      if (symbol_value < INSERT_SYMBOL_CHAR)
        *in_char_ptr++ = (unsigned char)symbol_value;
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
        *in_char_ptr++ = (unsigned char)((symbol_value >> 16) & 0xFF);
        *in_char_ptr++ = (unsigned char)((symbol_value >> 8) & 0xFF);
        *in_char_ptr++ = (unsigned char)(symbol_value & 0xFF);
      }
      else {
        symbol_value -= 0x80000000 + 0x100;
        *in_char_ptr++ = DEFINE_SYMBOL_CHAR;
        *in_char_ptr++ = (unsigned char)((symbol_value >> 16) & 0xFF);
        *in_char_ptr++ = (unsigned char)((symbol_value >> 8) & 0xFF);
        *in_char_ptr++ = (unsigned char)(symbol_value & 0xFF);
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
finish:
  free(back_nodes);
  free(match_start_nodes);
  free(match_list);
  free(start_symbol_ptr-1);
  fprintf(stderr,"Run time %0.3f seconds.\n", (float)((unsigned long long)clock()-start_time)/1000);
}
