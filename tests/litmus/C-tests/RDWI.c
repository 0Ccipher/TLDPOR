/* Copyright (C) 2018 Magnus Lång and Tuan Phong Ngo
 * This benchmark is part of SWSC */

#include <assert.h>
#include <stdint.h>
#include <stdatomic.h>
#include <pthread.h>

atomic_int vars[3]; 
atomic_int atom_1_r1_2; 
atomic_int atom_1_r2_0; 
atomic_int atom_1_r3_0; 
atomic_int atom_1_r4_1; 

void *t0(void *arg){
label_1:;
  atomic_store_explicit(&vars[2], 1, memory_order_seq_cst);

  atomic_store_explicit(&vars[1], 2, memory_order_seq_cst);
  return NULL;
}

void *t1(void *arg){
label_2:;
  int v2_r1 = atomic_load_explicit(&vars[1], memory_order_seq_cst);
  int v3_r9 = v2_r1 ^ v2_r1;
  int v6_r3 = atomic_load_explicit(&vars[0+v3_r9], memory_order_seq_cst);
  atomic_store_explicit(&vars[0], 1, memory_order_seq_cst);
  int v8_r4 = atomic_load_explicit(&vars[0], memory_order_seq_cst);
  int v9_r10 = v8_r4 ^ v8_r4;
  int v12_r2 = atomic_load_explicit(&vars[2+v9_r10], memory_order_seq_cst);
  int v20 = (v2_r1 == 2);
  atomic_store_explicit(&atom_1_r1_2, v20, memory_order_seq_cst);
  int v21 = (v12_r2 == 0);
  atomic_store_explicit(&atom_1_r2_0, v21, memory_order_seq_cst);
  int v22 = (v6_r3 == 0);
  atomic_store_explicit(&atom_1_r3_0, v22, memory_order_seq_cst);
  int v23 = (v8_r4 == 1);
  atomic_store_explicit(&atom_1_r4_1, v23, memory_order_seq_cst);
  return NULL;
}

int main(int argc, char *argv[]){
  pthread_t thr0; 
  pthread_t thr1; 

  atomic_init(&vars[2], 0);
  atomic_init(&vars[0], 0);
  atomic_init(&vars[1], 0);
  atomic_init(&atom_1_r1_2, 0);
  atomic_init(&atom_1_r2_0, 0);
  atomic_init(&atom_1_r3_0, 0);
  atomic_init(&atom_1_r4_1, 0);

  pthread_create(&thr0, NULL, t0, NULL);
  pthread_create(&thr1, NULL, t1, NULL);

  pthread_join(thr0, NULL);
  pthread_join(thr1, NULL);

  int v13 = atomic_load_explicit(&atom_1_r1_2, memory_order_seq_cst);
  int v14 = atomic_load_explicit(&atom_1_r2_0, memory_order_seq_cst);
  int v15 = atomic_load_explicit(&atom_1_r3_0, memory_order_seq_cst);
  int v16 = atomic_load_explicit(&atom_1_r4_1, memory_order_seq_cst);
  int v17_conj = v15 & v16;
  int v18_conj = v14 & v17_conj;
  int v19_conj = v13 & v18_conj;
  if (v19_conj == 1) assert(0);
  return 0;
}
