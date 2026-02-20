//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

// RUN: %revngcliftopt %s -emit-field-accesses -canonicalize 2>&1 | FileCheck %s

!void = !clift.primitive<void 0>
!generic64_t = !clift.primitive<generic 8>
!generic64_t$ptr = !clift.ptr<8 to !generic64_t>
!int32_t = !clift.primitive<signed 4>
!uint32_t = !clift.primitive<unsigned 4>
!int32_t$ptr = !clift.ptr<8 to !int32_t>

// Generic void function prototype with no argument
!f = !clift.func<
  "" as "f" : !void()
>

!s = !clift.struct<
  "1" : size(12) {
    "" : offset(0) !int32_t,
    "" : offset(4) !int32_t,
    "" : offset(8) !int32_t
  }
>
!s$ptr = !clift.ptr<8 to !s>

// Access, with offset computed with a `ptr_add` operation, to the third field
// of the `struct`

clift.func @f<!f>() {
  %0 = clift.local : !s
  clift.expr {
    %1 = clift.addressof %0 : !clift.ptr<8 to !s>
    %2 = clift.imm 1 : !generic64_t
    %3 = clift.ptr_add %1, %2 : (!s$ptr, !generic64_t)
    %4 = clift.cast<bitcast> %3 : !s$ptr -> !clift.ptr<8 to !int32_t>
    clift.yield %4 : !int32_t$ptr
  }
}

// CHECK-LABEL: clift.func @f<!f>
// CHECK: [[STRUCT:%[0-9]+]] = clift.local : !_1_
// CHECK: [[ADDRESSOF1:%[0-9]+]] = clift.addressof [[STRUCT]]
// CHECK: [[ACCESS:%[0-9]+]] = clift.access<indirect 2> [[ADDRESSOF1]]
// CHECK: [[ADDRESSOF2:%[0-9]+]] = clift.addressof [[ACCESS]]
// CHECK: [[CAST1:%[0-9]+]] = clift.cast<bitcast> [[ADDRESSOF2]]
// CHECK: [[CAST2:%[0-9]+]] = clift.cast<bitcast> [[CAST1]]
// CHECK: clift.yield [[CAST2]]
