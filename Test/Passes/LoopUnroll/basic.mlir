// RUN: veir-opt %s -p='loop-unroll{print-candidates}' 2>&1 | filecheck %s

// CHECK: loop-unroll: unrolled 3 of 3 CFG candidate(s)

"builtin.module"() ({
  // The true successor is the backedge. Check that both the induction variable and the
  // accumulator of the second iteration consume values produced by the first iteration.
  "llvm.func"() <{function_type = !llvm.func<i32 (i32)>, sym_name = "backedge_true"}> ({
  ^entry(%initial : i32):
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %eight = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
    "llvm.br"(%zero, %initial) [^loop] : (i32, i32) -> ()
  ^loop(%iv : i32, %acc : i32):
    %updated = "llvm.add"(%acc, %iv) : (i32, i32) -> i32
    %next = "llvm.add"(%iv, %one) : (i32, i32) -> i32
    %continue = "llvm.icmp"(%next, %eight) <{predicate = 1 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%continue, %next, %updated, %updated) [^loop, ^exit]
      <{operandSegmentSizes = array<i32: 1, 2, 1>}> : (i1, i32, i32, i32) -> ()
  ^exit(%result : i32):
    "llvm.return"(%result) : (i32) -> ()
  }) : () -> ()

  // CHECK-LABEL: "sym_name" = "backedge_true"
  // CHECK:       %[[ONE:[0-9]+]] = "llvm.mlir.constant"() <{{.*}}1 : i32
  // CHECK:       %[[BOUND:[0-9]+]] = "llvm.mlir.constant"() <{{.*}}8 : i32
  // CHECK:       ^{{[0-9]+}}(%[[IV:arg[0-9]+_0]] : i32, %[[ACC:arg[0-9]+_1]] : i32):
  // CHECK-NEXT:  %[[ACC1:[0-9]+]] = "llvm.add"(%[[ACC]], %[[IV]])
  // CHECK-NEXT:  %[[IV1:[0-9]+]] = "llvm.add"(%[[IV]], %[[ONE]])
  // CHECK-NEXT:  %[[ACC2:[0-9]+]] = "llvm.add"(%[[ACC1]], %[[IV1]])
  // CHECK-NEXT:  %[[IV2:[0-9]+]] = "llvm.add"(%[[IV1]], %[[ONE]])
  // CHECK-NEXT:  %[[CONTINUE:[0-9]+]] = "llvm.icmp"(%[[IV2]], %[[BOUND]])
  // CHECK-NEXT:  "llvm.cond_br"(%[[CONTINUE]], %[[IV2]], %[[ACC2]], %[[ACC2]])

  // LLVM may invert the comparison and put the backedge in the false successor.
  "llvm.func"() <{function_type = !llvm.func<void ()>, sym_name = "backedge_false"}> ({
  ^entry:
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %eight = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
    "llvm.br"(%zero) [^loop] : (i32) -> ()
  ^loop(%iv : i32):
    %next = "llvm.add"(%iv, %one) : (i32, i32) -> i32
    %done = "llvm.icmp"(%next, %eight) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%done, %next) [^exit, ^loop]
      <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i32) -> ()
  ^exit:
    "llvm.return"() : () -> ()
  }) : () -> ()

  // CHECK-LABEL: "sym_name" = "backedge_false"
  // CHECK:       ^{{[0-9]+}}(%[[IV_FALSE:arg[0-9]+_0]] : i32):
  // CHECK-NEXT:  %[[IV_FALSE1:[0-9]+]] = "llvm.add"(%[[IV_FALSE]], %{{[0-9]+}})
  // CHECK-NEXT:  %[[IV_FALSE2:[0-9]+]] = "llvm.add"(%[[IV_FALSE1]], %{{[0-9]+}})
  // CHECK-NEXT:  %[[DONE:[0-9]+]] = "llvm.icmp"(%[[IV_FALSE2]], %{{[0-9]+}})
  // CHECK-NEXT:  "llvm.cond_br"(%[[DONE]], %[[IV_FALSE2]])

  // The odd remainder is peeled into the preheader before the factor-two loop.
  "llvm.func"() <{function_type = !llvm.func<void ()>, sym_name = "odd_trip_count"}> ({
  ^entry:
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %seven = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    "llvm.br"(%zero) [^loop] : (i32) -> ()
  ^loop(%iv : i32):
    %next = "llvm.add"(%iv, %one) : (i32, i32) -> i32
    %continue = "llvm.icmp"(%next, %seven) <{predicate = 1 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%continue, %next) [^loop, ^exit]
      <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i32) -> ()
  ^exit:
    "llvm.return"() : () -> ()
  }) : () -> ()

  // CHECK-LABEL: "sym_name" = "odd_trip_count"
  // CHECK:       %[[PEELED:[0-9]+]] = "llvm.add"(%{{[0-9]+}}, %{{[0-9]+}})
  // CHECK:       "llvm.br"(%[[PEELED]])
  // CHECK:       ^{{[0-9]+}}(%[[ODD_IV:arg[0-9]+_0]] : i32):
  // CHECK-NEXT:  %[[ODD_NEXT1:[0-9]+]] = "llvm.add"(%[[ODD_IV]], %{{[0-9]+}})
  // CHECK-NEXT:  %[[ODD_NEXT2:[0-9]+]] = "llvm.add"(%[[ODD_NEXT1]], %{{[0-9]+}})
  // CHECK-NEXT:  %[[ODD_CONTINUE:[0-9]+]] = "llvm.icmp"(%[[ODD_NEXT2]], %{{[0-9]+}})
  // CHECK-NEXT:  "llvm.cond_br"(%[[ODD_CONTINUE]], %[[ODD_NEXT2]])

  // A conditional branch without a self-edge is not a CFG candidate.
  "llvm.func"() <{function_type = !llvm.func<void (i1)>, sym_name = "diamond"}> ({
  ^entry(%condition : i1):
    "llvm.cond_br"(%condition) [^left, ^right]
      <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^left:
    "llvm.br"() [^exit] : () -> ()
  ^right:
    "llvm.br"() [^exit] : () -> ()
  ^exit:
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
