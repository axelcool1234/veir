// RUN: veir-interpret %s | filecheck %s --check-prefix=EXEC
// RUN: veir-opt %s -p=loop-unroll > %t && veir-interpret %t | filecheck %s --check-prefix=EXEC
// RUN: veir-opt %s -p='loop-unroll{factor=3}' > %t && veir-interpret %t | filecheck %s --check-prefix=EXEC
// RUN: veir-opt %s -p='loop-unroll{factor=4}' > %t && veir-interpret %t | filecheck %s --check-prefix=EXEC

// EXEC: Program output: #[0x0000001c#32]

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 ()>, sym_name = "main"}> ({
  ^entry:
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %eight = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
    "llvm.br"(%zero, %zero) [^loop] : (i32, i32) -> ()
  ^loop(%iv : i32, %sum : i32):
    %updated = "llvm.add"(%sum, %iv) : (i32, i32) -> i32
    %next = "llvm.add"(%iv, %one) : (i32, i32) -> i32
    %continue = "llvm.icmp"(%next, %eight) <{predicate = 1 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%continue, %next, %updated, %updated) [^loop, ^exit]
      <{operandSegmentSizes = array<i32: 1, 2, 1>}> : (i1, i32, i32, i32) -> ()
  ^exit(%result : i32):
    "llvm.return"(%result) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
