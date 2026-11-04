// RUN: not veir-opt %s -p='mod-arith-to-arith{pow2-widht}' 2>&1 | filecheck %s --check-prefix=MISSPELLED
// RUN: MLIR_INVALID
// RUN: not veir-opt %s -p='cse{whatever}' 2>&1 | filecheck %s --check-prefix=NO-OPTIONS
// RUN: not veir-opt %s -p='mod-arith{pow2-width}' 2>&1 | filecheck %s --check-prefix=GROUP
// RUN: not veir-opt %s -p='mod-arith-to-arith{pow2-width' 2>&1 | filecheck %s --check-prefix=UNCLOSED
// RUN: not veir-opt %s -p='mod-arith-to-arith{barrett=maybe}' 2>&1 | filecheck %s --check-prefix=BAD-BOOL
// RUN: not veir-opt %s -p='loop-unroll{factor}' 2>&1 | filecheck %s --check-prefix=MISSING-NAT
// RUN: not veir-opt %s -p='loop-unroll{factor=many}' 2>&1 | filecheck %s --check-prefix=BAD-NAT
// RUN: not veir-opt %s -p='loop-unroll{factor=1}' 2>&1 | filecheck %s --check-prefix=SMALL-FACTOR

// A pass name in a `-p` list may be followed by a brace-enclosed, space-separated list of
// typed options. A bare boolean name means true, booleans also accept `name=true|false`, and
// natural number options require `name=value`. These check malformed syntax; behavior is covered
// by ModArithToArith/mul.mlir, LoopUnroll/generated_from_c.c, and
// FunctionBoundaryCoercion/mod_arith_pow2_width.mlir.

"builtin.module"() ({
}) : () -> ()

// MISSPELLED: pass 'mod-arith-to-arith' has no option 'pow2-widht' (it accepts: barrett, pow2-width)
// NO-OPTIONS: pass 'cse' has no option 'whatever' (it accepts no options)
// GROUP: pass group 'mod-arith' does not take options
// UNCLOSED: missing closing brace in the options of pass 'mod-arith-to-arith'
// BAD-BOOL: invalid value 'maybe' for boolean option 'barrett' of pass 'mod-arith-to-arith'
// MISSING-NAT: natural number option 'factor' of pass 'loop-unroll' requires a value
// BAD-NAT: invalid value 'many' for natural number option 'factor' of pass 'loop-unroll'
// SMALL-FACTOR: pass 'loop-unroll' failed: factor must be at least 2
