/* Copyright (C) 2018 Magnus Lång and Tuan Phong Ngo
 * This benchmark is part of SWSC */

#include <assert.h>
#include <stdint.h>
#include <stdatomic.h>
#include <pthread.h>

atomic_int vars[2]; 
atomic_int atom_0_r3_2; 
atomic_int atom_2_r1_1; 
atomic_int atom_3_r1_3; 
atomic_int atom_3_r4_0; 

void *t0(void *arg){
label_1:;
  atomic_store_explicit(&vars[0], 1, memory_order_seq_cst);
  int v2_r3 = atomic_load_explicit(&vars[0], memory_order_seq_cst);
  int v3_r4 = v2_r3 ^ v2_r3;
  atomic_store_explicit(&vars[1+v3_r4], 1, memory_order_seq_cst);
  atomic_store_explicit(&vars[1], 3, memory_order_seq_cst);
  int v22 = (v2_r3 == 2);
  atomic_store_explicit(&atom_0_r3_2, v22, memory_order_seq_cst);
  return NULL;
}

void *t1(void *arg){
label_2:;
  atomic_store_explicit(&vars[0], 2, memory_order_seq_cst);
  return NULL;
}

void *t2(void *arg){
label_3:;
  int v5_r1 = atomic_load_explicit(&vars[1], memory_order_seq_cst);
  atomic_store_explicit(&vars[1], 2, memory_order_seq_cst);
  int v23 = (v5_r1 == 1);
  atomic_store_explicit(&atom_2_r1_1, v23, memory_order_seq_cst);
  return NULL;
}

void *t3(void *arg){
label_4:;
  int v7_r1 = atomic_load_explicit(&vars[1], memory_order_seq_cst);
  int v8_r3 = v7_r1 ^ v7_r1;
  int v11_r4 = atomic_load_explicit(&vars[0+v8_r3], memory_order_seq_cst);
  int v24 = (v7_r1 == 3);
  atomic_store_explicit(&atom_3_r1_3, v24, memory_order_seq_cst);
  int v25 = (v11_r4 == 0);
  atomic_store_explicit(&atom_3_r4_0, v25, memory_order_seq_cst);
  return NULL;
}

int main(int argc, char *argv[]){
  pthread_t thr0; 
  pthread_t thr1; 
  pthread_t thr2; 
  pthread_t thr3; 

  atomic_init(&vars[1], 0);
  atomic_init(&vars[0], 0);
  atomic_init(&atom_0_r3_2, 0);
  atomic_init(&atom_2_r1_1, 0);
  atomic_init(&atom_3_r1_3, 0);
  atomic_init(&atom_3_r4_0, 0);

  pthread_create(&thr0, NULL, t0, NULL);
  pthread_create(&thr1, NULL, t1, NULL);
  pthread_create(&thr2, NULL, t2, NULL);
  pthread_create(&thr3, NULL, t3, NULL);

  pthread_join(thr0, NULL);
  pthread_join(thr1, NULL);
  pthread_join(thr2, NULL);
  pthread_join(thr3, NULL);

  int v12 = atomic_load_explicit(&atom_0_r3_2, memory_order_seq_cst);
  int v13 = atomic_load_explicit(&vars[1], memory_order_seq_cst);
  int v14 = (v13 == 3);
  int v15 = atomic_load_explicit(&atom_2_r1_1, memory_order_seq_cst);
  int v16 = atomic_load_explicit(&atom_3_r1_3, memory_order_seq_cst);
  int v17 = atomic_load_explicit(&atom_3_r4_0, memory_order_seq_cst);
  int v18_conj = v16 & v17;
  int v19_conj = v15 & v18_conj;
  int v20_conj = v14 & v19_conj;
  int v21_conj = v12 & v20_conj;
  if (v21_conj == 1) assert(0);
  return 0;
}
