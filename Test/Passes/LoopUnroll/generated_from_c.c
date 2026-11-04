// REQUIRES: clang, opt, mlir-translate, mlir-opt
// RUN: clang -O0 -Xclang -disable-O0-optnone -S -emit-llvm %s -o %t.raw.ll
// RUN: opt -passes='mem2reg,loop-simplify,loop-rotate,indvars,simplifycfg' \
// RUN:   -S %t.raw.ll -o %t.canonical.ll
// RUN: mlir-translate --import-llvm %t.canonical.ll | \
// RUN:   mlir-opt --mlir-print-op-generic --mlir-print-local-scope > %t.mlir
// RUN: veir-opt %t.mlir -p='loop-unroll{print-candidates}' 2>&1 | filecheck %s
// RUN: veir-opt %t.mlir -p='loop-unroll{factor=3 print-candidates}' 2>&1 | \
// RUN:   filecheck %s --check-prefix=FACTOR3
// RUN: clang -O1 -fno-unroll-loops -fno-vectorize -fno-slp-vectorize \
// RUN:   -S -emit-llvm %s -o %t.o1.ll
// RUN: mlir-translate --import-llvm %t.o1.ll | \
// RUN:   mlir-opt --mlir-print-op-generic --mlir-print-local-scope > %t.o1.mlir
// RUN: veir-opt %t.o1.mlir -p='loop-unroll{print-candidates}' 2>&1 | \
// RUN:   filecheck %s --check-prefix=O1
// RUN: veir-opt %t.o1.mlir -p='loop-unroll{factor=3 print-candidates}' 2>&1 | \
// RUN:   filecheck %s --check-prefix=FACTOR3-O1

// CHECK: loop-unroll: unrolled 4 of 5 CFG candidate(s)
// O1: loop-unroll: unrolled 4 of 5 CFG candidate(s)
// FACTOR3: loop-unroll: unrolled 4 of 5 CFG candidate(s)
// FACTOR3-O1: loop-unroll: unrolled 4 of 5 CFG candidate(s)

void add8(int *values, int increment) {
  for (int i = 0; i < 8; ++i)
    values[i] += increment;
}

// CHECK-LABEL: "sym_name" = "add8"
// CHECK:       "llvm.store"
// CHECK:       "llvm.store"

int sum8(const int *values) {
  int sum = 0;
  for (int i = 0; i < 8; ++i)
    sum += values[i];
  return sum;
}

// CHECK-LABEL: "sym_name" = "sum8"
// CHECK:       "llvm.load"
// CHECK:       "llvm.load"

extern int step(int value, int iteration);

int recurrence8(int initial) {
  int value = initial;
  for (int i = 0; i < 8; ++i)
    value = step(value, i);
  return value;
}

// CHECK-LABEL: "sym_name" = "recurrence8"
// CHECK:       "llvm.call"
// CHECK:       "llvm.call"
// O1-LABEL:    "sym_name" = "recurrence8"
// O1:          "llvm.return"(%[[SECOND_CALL:[0-9]+]])
// O1:          %[[FIRST_CALL:[0-9]+]] = "llvm.call"
// O1:          %[[SECOND_CALL]] = "llvm.call"
// O1:          "llvm.cond_br"
// FACTOR3-LABEL: "sym_name" = "recurrence8"
// FACTOR3-COUNT-5: "llvm.call"
// FACTOR3-NOT: "llvm.call"
// FACTOR3-O1-LABEL: "sym_name" = "recurrence8"
// FACTOR3-O1-COUNT-2: "llvm.call"
// FACTOR3-O1: "llvm.return"(%[[FACTOR3_RESULT:[0-9]+]])
// FACTOR3-O1-COUNT-2: "llvm.call"
// FACTOR3-O1: %[[FACTOR3_RESULT]] = "llvm.call"
// FACTOR3-O1-NOT: "llvm.call"

unsigned mix8(unsigned initial) {
  unsigned value = initial;
  for (unsigned i = 0; i < 8; ++i)
    value = value * 1664525u + i;
  return value;
}

// CHECK-LABEL: "sym_name" = "mix8"
// CHECK:       "llvm.mul"
// CHECK:       "llvm.mul"

int sum_n(const int *values, int n) {
  int sum = 0;
  for (int i = 0; i < n; ++i)
    sum += values[i];
  return sum;
}

// A runtime trip count is outside the current pass contract and remains single-copy.
// CHECK-LABEL: "sym_name" = "sum_n"
// CHECK:       "llvm.load"
// CHECK-NOT:   "llvm.load"
