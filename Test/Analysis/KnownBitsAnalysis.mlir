// RUN: veir-opt %s -p=print-known-bits | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i8) -> (), sym_name = "known_bits"}> ({
  ^entry(%x : i8):
    // CHECK:      // dataflow.known_bits block argument 0 = ????????
    %unknown_mask = "arith.constant"() <{value = 48 : i8}> : () -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.constant result 0 = 00110000
    %known_ones = "arith.constant"() <{value = 131 : i8}> : () -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.constant result 0 = 10000011
    %unknown_bits = "arith.andi"(%x, %unknown_mask) : (i8, i8) -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.andi result 0 = 00??0000
    %pattern = "arith.ori"(%unknown_bits, %known_ones) : (i8, i8) -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.ori result 0 = 10??0011
    %rhs = "arith.constant"() <{value = 240 : i8}> : () -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.constant result 0 = 11110000
    %and = "arith.andi"(%pattern, %rhs) : (i8, i8) -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.andi result 0 = 10??0000
    %or = "arith.ori"(%pattern, %rhs) : (i8, i8) -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.ori result 0 = 11110011
    %xor = "arith.xori"(%pattern, %rhs) : (i8, i8) -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.xori result 0 = 01??0011
    %srem = "arith.remsi"(%pattern, %rhs) : (i8, i8) -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.remsi result 0 = 11110011
    %urem = "arith.remui"(%pattern, %rhs) : (i8, i8) -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.remui result 0 = ????0011
    %poison_shift = "arith.shli"(%pattern, %rhs) : (i8, i8) -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.shli result 0 = 00000000
    %low_mask = "arith.constant"() <{value = 15 : i8}> : () -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.constant result 0 = 00001111
    %low = "arith.andi"(%x, %low_mask) : (i8, i8) -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.andi result 0 = 0000????
    %sign = "arith.constant"() <{value = 128 : i8}> : () -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.constant result 0 = 10000000
    %high = "arith.ori"(%low, %sign) : (i8, i8) -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.ori result 0 = 1000????
    %nuw = "arith.addi"(%low, %high) <{overflowFlags = #arith.overflow<nuw>}> : (i8, i8) -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.addi result 0 = 100?????
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
