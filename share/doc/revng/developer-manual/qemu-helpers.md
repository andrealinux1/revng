## Helper Functions

In rev.ng, *helper functions* are C functions originating from QEMU that implement the semantics of complex CPU instructions.

For instance, the x86 `div` instruction has non-trivial semantics (exception on division by zero, quotient overflow, etc.), so QEMU implements it in a C helper called `helper_divb_AL`.

These helpers are compiled to LLVM IR and shipped as part of `libtcg`.

In rev.ng, at *build* time, they undergo significant transformations that prepare them for use during lifting.
This document walks through how helpers evolve, using x86-64 as the driving example.

### The CPU state in QEMU

In QEMU, the entire CPU state lives in a C `struct` called `CPUArchState`.
For x86-64, the relevant fields look like this (from `target/i386/cpu.h`):

```c notest
typedef struct CPUArchState {
    // regs[0] = RAX, regs[1] = RCX....
    target_ulong regs[CPU_NB_REGS];
    target_ulong eip;
    target_ulong eflags;

    /* emulator internal eflags handling */
    target_ulong cc_dst;
    target_ulong cc_src;
    target_ulong cc_src2;
    uint32_t cc_op;
    int32_t df;
    uint32_t hflags; // TB flags, see HF_xxx constants
    uint32_t hflags2;

    /* segments */
    SegmentCache segs[6];
    SegmentCache ldt;
    SegmentCache tr;
    SegmentCache gdt;
    SegmentCache idt;

    target_ulong cr[5]; // cr[0] = CR0
    // ...

    float_status sse_status; // SSE rounding/exception state
    // ...
    ZMMReg xmm_regs[CPU_NB_REGS == 8 ? 8 : 32]; // XMM/YMM/ZMM registers
    ZMMReg xmm_t0; // temporary XMM register
    // ...
} CPUArchState;
```

Every helper takes a `CPUArchState *env` pointer as its first argument and reads or writes the CPU state through it.

### `REVNG_INLINE` and `REVNG_EXCEPTIONAL`

In the QEMU source, helpers are tagged with section attributes that control how rev.ng handles them.
When compiling helpers to LLVM IR, these expand to section attributes:

```c notest
#define REVNG_INLINE __attribute__((section("revng_inline")))
#define REVNG_EXCEPTIONAL __attribute__((section("revng_exceptional")))
```

`REVNG_INLINE` marks helpers whose body rev.ng will inline at a certain point in the [pipeline](../references/pipeline/).
Helpers *not* tagged with `REVNG_INLINE` are kept as opaque calls.

`REVNG_EXCEPTIONAL` marks helpers that are considered to be "exceptional cases", like division by 0 or an invalid memory access. At a certain point in the pipeline, we assume these situations don't happen. This enables us to remove these calls (and all the code they postdominate) and emit better looking code.

### Example helpers

Let's now see some example helper functions, as they are in QEMU.

Let's consider `helper_clts`, a `REVNG_INLINE` helper implementing the x86 `clts` instruction (clear Task-Switch flag in CR0).
The TS (Task-Switch) flag is bit 3 of CR0.
The CPU sets it on every hardware task switch; when set, any FP or SSE instruction traps with a `#NM` (Device Not Available) exception, allowing the OS to lazily save and restore floating-point state.
The `clts` instruction clears this flag, and the helper mirrors it into the internal `hflags` register:

```c notest
void helper_clts(CPUX86State *env) REVNG_INLINE
{
    env->cr[0] &= ~CR0_TS_MASK;
    env->hflags &= ~HF_TS_MASK;
}
```

Let's then consider `helper_divb_AL`, a `REVNG_INLINE` helper implementing the x86 `div r/m8` instruction (unsigned byte division).
This instruction divides `AX` (the low 16 bits of `RAX`, the *implicit* dividend) by an 8-bit operand (the *explicit* divisor, passed as `t0`).
The quotient is stored in `AL` and the remainder in `AH` (both packed back into `RAX`).
A `#DE` (divide error) exception is raised if the divisor is zero or if the quotient exceeds 0xFF:

```c notest
void helper_divb_AL(CPUX86State *env, target_ulong t0) REVNG_INLINE
{
    unsigned int num, den, q, r;

    num = (env->regs[R_EAX] & 0xffff);
    den = (t0 & 0xff);
    if (den == 0) {
        raise_exception_ra(env, EXCP00_DIVZ, GETPC());
    }
    q = (num / den);
    if (q > 0xff) {
        raise_exception_ra(env, EXCP00_DIVZ, GETPC());
    }
    q &= 0xff;
    r = (num % den) & 0xff;
    env->regs[R_EAX] = (env->regs[R_EAX] & ~0xffff) | (r << 8) | q;
}
```

On the exceptional paths, `raise_exception_ra` is a `REVNG_EXCEPTIONAL` function.

Finally, `helper_write_eflags` is a helper *without* `REVNG_INLINE`.

```c notest
void helper_write_eflags(CPUX86State *env, target_ulong t0,
                         uint32_t update_mask)
{
    cpu_load_eflags(env, t0, update_mask);
}
```

### The original helpers in LLVM IR

The original helpers live in `share/libtcg/libtcg-helpers-x86_64.bc`.

!!! tip

    In the following snippets we apply the LLVM `-sroa` (Scalar Replacement of Aggregates), `-instcombine` (instruction combining) and `-dce` (dead code elimination) passes to the IR.
    This eliminates stack allocations, promotes local variables to SSA values, folds redundant GEPs and removes dead instructions, making the IR much easier to read.

We also define a `pretty` shell function that strips LLVM attribute-group references, metadata annotations and trailing comments from the textual IR, and then renumbers per-function SSA values and basic-block labels to a stable per-snippet `%v1, %v2, …` / `v1:, v2:, …` form so that the snippets stay valid even when upstream passes shift the original instruction count:

```bash
$ ROOT="$(dirname "$(dirname "$(which revng)")")"
$ pretty() { sed "s/ #[0-9]*//; s/ ![^ ]*//g; s/;.*//" | awk 'function rename(n) { if (!(n in r)) { c++; r[n] = c } return r[n] } { line = $0; out = ""; while (match(line, /%[0-9]+/)) { out = out substr(line, 1, RSTART - 1) "%v" rename(substr(line, RSTART + 1, RLENGTH - 1)); line = substr(line, RSTART + RLENGTH) } out = out line; if (match(out, /^[0-9]+:/)) { out = "v" rename(substr(out, 1, RLENGTH - 1)) ":" substr(out, RLENGTH + 1) } print out }'; }
$ revng opt -strip-debug -sroa -instcombine -dce -S \
    "$ROOT/share/libtcg/libtcg-helpers-x86_64.bc" \
    | sed -n "/^define void @helper_clts/,/^}/p" \
    | pretty
define void @helper_clts(ptr noundef %v1) section "revng_inline" {
  %v2 = getelementptr inbounds %struct.CPUArchState, ptr %v1, i64 0, i32 15
  %v3 = load i64, ptr %v2, align 8
  %v4 = and i64 %v3, u0xfffffff7
  store i64 %v4, ptr %v2, align 8
  %v5 = getelementptr inbounds %struct.CPUArchState, ptr %v1, i64 0, i32 8
  %v6 = load i32, ptr %v5, align 16
  %v7 = and i32 %v6, u0xfffff7ff
  store i32 %v7, ptr %v5, align 16
  ret void
}
```

The function takes a `%struct.CPUArchState` pointer `%v1` (the `env` argument; the `0` in the original `%0` is the implicit slot number, which `pretty` renumbers to `1`) and navigates into it using `getelementptr`:

- Field index 15 is `cr[0]` (the first element of the `cr` array). It loads the value, clears the TS bit (`and` with `0xfffffff7`), and stores it back.
- Field index 8 is `hflags`, an `i32`. It clears the `HF_TS_MASK` bit.

Now let's look at `helper_divb_AL`:

```bash
$ revng opt -strip-debug -sroa -instcombine -dce -S \
    "$ROOT/share/libtcg/libtcg-helpers-x86_64.bc" \
    | sed -n "/^define void @helper_divb_AL/,/^}/p" \
    | pretty \
    | head -16
define void @helper_divb_AL(ptr noundef %v1, i64 noundef %v2) section "revng_inline" {
  %v3 = load i64, ptr %v1, align 16
  %v4 = trunc i64 %v3 to i32
  %v5 = and i32 %v4, u0xffff
  %v6 = trunc i64 %v2 to i32
  %v7 = and i32 %v6, 255
  %v8 = icmp eq i32 %v7, 0
  br i1 %v8, label %v9, label %v10

v9:
  call void @raise_exception_ra(ptr noundef nonnull %v1, i32 noundef 0, i64 noundef 0)
  unreachable

v10:
  %v11 = udiv i32 %v5, %v7
  %v12 = icmp ugt i32 %v11, 255
```

Since `regs` is the first field of `CPUArchState` and `R_EAX` is index 0, `instcombine` folds the GEP chain away and loads directly from `%v1` (the `env` argument).
The function loads `RAX`, masks the low 16 bits (`num = env->regs[R_EAX] & 0xffff`), truncates the divisor `%v2` to 8 bits, and checks for division by zero.
Notice the call to `raise_exception_ra` followed by `unreachable`.

All these accesses go through the `env` struct pointer.

This is a problem for rev.ng: during lifting, the CPU state is not a struct in memory but a set of independent global variables called *CSVs* (CPU State Variables).
The build-time passes solve exactly this.

### Build-time processing

At build time, the helpers undergo a chain of transformations.
Each step produces a new bitcode file derived from the previous one:

1. QEMU's C helper sources are compiled to LLVM IR, producing the *original* helpers in `share/libtcg/libtcg-helpers-x86_64.bc`. These still access the CPU state through the `env` struct pointer.

2. The *full* module (`share/revng/libtcg-helpers-full-x86_64.bc`) is derived from the original by running the `fix-helpers` pass, which replaces every `env` struct access with an access to the corresponding CSV. All helper bodies are present. For x86-64 this is ~53 MB.

3. The *to-inline* module (`share/revng/libtcg-helpers-to-inline-x86_64.bc`) is derived from the full module by stripping the bodies of all helpers *not* tagged with `REVNG_INLINE`. Only `REVNG_INLINE` helpers retain their bodies. ~3 MB.

4. The *declarations-only* module (`share/revng/libtcg-helpers-declarations-only-x86_64.bc`) is also derived from the full module, but goes further: *all* helper bodies are stripped, leaving only declarations with CSV access metadata.

The size difference matters: linking unnecessary code slows down the pipeline without bringing any benefit.
Each pipeline stage links only what it needs:

* the `lift` step links the *declarations-only* module — it only needs function signatures and CSV access metadata to emit calls;
* `inline-helpers` links the *to-inline* module and inlines the `REVNG_INLINE` bodies into the lifted code;
* `recompile` needs every helper implementation, so it links the large *full* module.

### The full helpers

Let's look at `helper_clts` after the `fix-helpers` transformation:

```bash
$ revng opt -strip-debug -instcombine -dce -S \
    "$ROOT/share/revng/libtcg-helpers-full-x86_64.bc" \
    | sed -n "/^define void @helper_clts/,/^}/p" \
    | pretty
define void @helper_clts(ptr noundef %v1) section "revng_inline" {
  %v2 = load i64, ptr @_state_0x2968, align 8
  %v3 = and i64 %v2, u0xfffffff7
  store i64 %v3, ptr @_state_0x2968, align 8
  %v4 = load i32, ptr @_state_0x2870, align 4
  %v5 = and i32 %v4, u0xfffff7ff
  store i32 %v5, ptr @_state_0x2870, align 4
  ret void
}
```

Instead of loading and storing through the `env` struct pointer, the helper now reads from and writes to *CSVs*: `@_state_0x2968` for `cr[0]` and `@_state_0x2870` for `hflags`.
The dead `getelementptr` and `ptrtoint` instructions left over from the annotation have been eliminated by `instcombine`.

The hex number in a CSV name is the byte offset of the field within the broader `CPUState` struct (which wraps `CPUArchState`).
Well-known registers get human-readable names instead.
For instance, `helper_divb_AL` after annotation:

```bash
$ revng opt -strip-debug -instcombine -dce -S \
    "$ROOT/share/revng/libtcg-helpers-full-x86_64.bc" \
    | sed -n "/^define void @helper_divb_AL/,/^}/p" \
    | pretty \
    | head -10
define void @helper_divb_AL(ptr noundef %v1, i64 noundef %v2) section "revng_inline" {
  %v3 = load i64, ptr @_rax, align 8
  %v4 = trunc i64 %v3 to i32
  %v5 = and i32 %v4, u0xffff
  %v6 = trunc i64 %v2 to i32
  %v7 = and i32 %v6, 255
  %v8 = icmp eq i32 %v7, 0
  br i1 %v8, label %v9, label %v10

v9:
```

Here `@_rax` (the CSV for the `rax` register) replaces the `getelementptr` + `load` through `env->regs[R_EAX]`.

#### Multiple CSVs for a single access

In `helper_clts` and `helper_divb_AL`, each memory access through `env` targets exactly one field. The `fix-helpers` pass can replace each access with a direct load/store of the corresponding CSV.

Not all helpers are that simple. Consider `helper_addsd`, which implements the x86 `addsd` instruction (add scalar double-precision floating-point).
It takes three `ZMMReg *` pointer arguments (`d`, `v`, `s`) that can each point to *any* XMM register in `xmm_regs[0..31]` or the temporary `xmm_t0`:

```c notest
void helper_addsd(CPUX86State *env, ZMMReg *d, ZMMReg *v, ZMMReg *s)
        REVNG_INLINE
{
    d->ZMM_D(0) = float64_add(v->ZMM_D(0), s->ZMM_D(0),
                               &env->sse_status);
    d->ZMM_Q(1) = v->ZMM_Q(1);
}
```

In the original IR, the accesses are simple pointer dereferences (`load i64, ptr %2`).
But in the full module, `fix-helpers` cannot replace them with a single CSV — the same pointer could refer to any of 33 different registers.
Instead, it emits a `switch` on the pointer value (which is the byte offset of the register within `CPUState`) to dispatch to the correct CSV:

```bash
$ revng opt -strip-debug -instcombine -dce -S \
    "$ROOT/share/revng/libtcg-helpers-full-x86_64.bc" \
    | sed -n "/^define void @helper_addsd/,/^}/p" \
    | pretty \
    | sed -n '1,12p'
define void @helper_addsd(ptr noundef %v1, ptr noundef %v2, ptr noundef %v3, ptr noundef %v4) section "revng_inline" {
  %v5 = ptrtoint ptr %v3 to i64
  switch i64 %v5, label %v6 [
    i64 u0x2f10, label %v7
    i64 u0x2f50, label %v8
    i64 u0x2e90, label %v9
    i64 u0x2e50, label %v10
    i64 u0x3010, label %v11
    i64 u0x2b10, label %v12
    i64 u0x3150, label %v13
    i64 u0x2bd0, label %v14
    i64 u0x3050, label %v15
```

Each case label corresponds to the offset of a different XMM register (e.g. `0x2b10` is `xmm_regs[0]`, `0x2b50` is `xmm_regs[1]`, etc., stepping by 64 bytes).
In each case, the load is replaced by a direct access to the corresponding CSV.

### The to-inline helpers

The *to-inline* variant keeps function *bodies* only for helpers marked with `REVNG_INLINE`.
All other helpers are dropped entirely.

For example, `helper_clts` (which is `REVNG_INLINE`) still has its full definition:

```bash
$ revng opt -strip-debug -S \
    "$ROOT/share/revng/libtcg-helpers-to-inline-x86_64.bc" \
    | grep "^define.*@helper_clts" \
    | pretty
define void @helper_clts(ptr noundef %v1) section "revng_inline" {
```

The *to-inline* module contains only the `REVNG_INLINE` helpers as definitions — a strict subset of the declarations the full module has. To keep this stable against helper-set changes we just verify the relationship rather than print a literal count:

```bash
$ TO_INLINE_DEFS=$(revng opt -strip-debug -S \
    "$ROOT/share/revng/libtcg-helpers-to-inline-x86_64.bc" | grep -c "^define")
$ ALL_HELPERS=$(revng opt -strip-debug -S \
    "$ROOT/share/revng/libtcg-helpers-declarations-only-x86_64.bc" \
    | grep "^declare" | grep -c "helper_")
$ test "$TO_INLINE_DEFS" -gt 0 -a "$TO_INLINE_DEFS" -lt "$ALL_HELPERS" \
    && echo "to-inline has fewer definitions than the total helpers"
to-inline has fewer definitions than the total helpers
```

### The declarations-only helpers

The *declarations-only* variant (`share/revng/libtcg-helpers-declarations-only-x86_64.bc`) goes one step further: *no* helper has a body.
Every function, including `REVNG_INLINE` ones, is a bare declaration.

```bash
$ revng opt -strip-debug -S \
    "$ROOT/share/revng/libtcg-helpers-declarations-only-x86_64.bc" \
    | grep "^declare.*@helper_clts" \
    | pretty
declare void @helper_clts(ptr noundef) section "revng_inline"
```

The module has no definitions, only declarations. We verify the qualitative property — zero definitions and many helper declarations — without committing to a literal count of the latter:

```bash
$ echo "Definitions:"
$ revng opt -strip-debug -S \
    "$ROOT/share/revng/libtcg-helpers-declarations-only-x86_64.bc" \
    | { grep -c "^define" || true; }
Definitions:
0
$ HELPER_DECLS=$(revng opt -strip-debug -S \
    "$ROOT/share/revng/libtcg-helpers-declarations-only-x86_64.bc" \
    | grep "^declare" | grep -c "helper_")
$ test "$HELPER_DECLS" -gt 100 && echo "Helper declarations: many (more than 100)"
Helper declarations: many (more than 100)
```

### CSV access metadata

All helper variants carry `!revng.csvaccess.offsets.load` and `!revng.csvaccess.offsets.store` metadata on every helper.
This metadata records which CSVs a helper reads and which it writes, *even when no body is available*.

For instance, in the *declarations-only* module, `helper_write_eflags` has no body, yet its declaration carries the metadata. The actual metadata-node IDs (`!114`, `!118`, …) shift as the module accumulates or drops metadata, so we replace them with a `!N` placeholder before printing the line — only the *names* of the attached metadata kinds are stable:

```bash
$ revng opt -strip-debug -S \
    "$ROOT/share/revng/libtcg-helpers-declarations-only-x86_64.bc" \
    | grep "^declare.*@helper_write_eflags" \
    | sed -E 's/ !([a-zA-Z][a-zA-Z0-9.]*) ![0-9]+/ !\1 !N/g; s/ #[0-9]+$//'
declare !revng.csua !N !revng.csvaccess.offsets.load !N !revng.csvaccess.offsets.store !N !revng.tags !N void @helper_write_eflags(ptr noundef, i64 noundef, i32 noundef)
```

The `!revng.csvaccess.offsets.load` and `!revng.csvaccess.offsets.store` references point at metadata nodes defined at the end of the module. Each is a `!{i32 0, !<csv-list>}` tuple where `!<csv-list>` is `!{!"name1", !"name2", ...}` — the actual CSVs the helper reads or writes. To extract those names without committing to any specific metadata-node ID, we look up the IDs on-the-fly:

```bash
$ IR=$(revng opt -strip-debug -S \
    "$ROOT/share/revng/libtcg-helpers-declarations-only-x86_64.bc")
$ DECL=$(echo "$IR" | grep "^declare.*@helper_write_eflags")
$ for kind in load store; do \
    PARENT=$(echo "$DECL" \
      | grep -oE "csvaccess.offsets.$kind ![0-9]+" \
      | grep -oE "[0-9]+") ; \
    CHILD=$(echo "$IR" | grep "^!$PARENT = " \
      | grep -oE "![0-9]+\}" | grep -oE "[0-9]+") ; \
    echo "$kind:" ; \
    echo "$IR" | grep "^!$CHILD = " \
      | grep -oE '"[^"]+"' | tr -d '"' ; \
  done
load:
_state_0x2848
store:
_cc_src
_state_0x286c
_state_0x2848
_cc_op
```

So `helper_write_eflags` reads `_state_0x2848` (the `eflags` field) and writes four CSVs: `_cc_src`, `_state_0x286c` (the `df` field), `_state_0x2848` (the `eflags` field), and `_cc_op`.

This is critical for the *declarations-only* module: analyses can determine the side effects of a helper call purely from metadata, without inspecting a body that is not present.

### Usage in the pipeline

Each variant is used by a different stage of the rev.ng [pipeline](../references/pipeline/).

#### Helpers in the `lift` artifact

At lift time, the *declarations-only* module is linked in.
The lifter only needs function signatures to emit calls; it does not need bodies.
The CSV access metadata is enough to inform analyses about what each helper reads and writes.

In the following, we create a minimal binary that divides the first argument (`rdi`) by the low byte of the second (`sil`), which triggers a call to `helper_divb_AL`.
The model tells rev.ng the binary's architecture, memory layout, and function prototypes.
We declare a single function at `0x400000` with a two-argument prototype:

```yaml title="model.yml"
---
# C prototype: uint64_t func(uint64_t arg0, uint64_t arg1)
Architecture: x86_64
DefaultABI: SystemV_x86_64
Segments:
  - StartAddress: "0x400000:Generic64"
    VirtualSize: 6
    StartOffset: 0
    FileSize: 6
    IsReadable: true
    IsWriteable: false
    IsExecutable: true
Functions:
  - Entry: "0x400000:Code_x86_64"
    Prototype:
      Kind: DefinedType
      Definition: "/TypeDefinitions/0-CABIFunctionDefinition"
TypeDefinitions:
  - Kind: CABIFunctionDefinition
    ABI: SystemV_x86_64
    ID: 0
    Arguments:
      - Index: 0
        Type:
          Kind: PrimitiveType
          PrimitiveKind: Unsigned
          Size: 8
      - Index: 1
        Type:
          Kind: PrimitiveType
          PrimitiveKind: Unsigned
          Size: 8
    ReturnType:
      Kind: PrimitiveType
      PrimitiveKind: Unsigned
      Size: 8
...
```

```bash
$ printf '\x89\xf8\x40\xf6\xf6\xc3\x90' > div-binary
$ objdump -D -Mintel,x86-64 -b binary -m i386:x86-64 div-binary

div-binary:     file format binary


Disassembly of section .data:

0000000000000000 <.data>:
   0: 89 f8                 mov    eax,edi
   2: 40 f6 f6              div    sil
   5: c3                    ret
   6: 90                    nop
```

```bash silent
$ revng artifact lift div-binary --model model.yml -o module.bc
```

Let's inspect the basic block.
The `mov eax, edi` copies the first argument into the accumulator; then `div sil` divides it by the low byte of the second argument:

```bash
$ revng opt -strip-debug -S module.bc \
    | sed -n '/^"bb.0x400000:Code_x86_64":/,/^$/p' \
    | pretty
"bb.0x400000:Code_x86_64":
  call void (ptr, i64, i32, i32, ptr, ...) @newpc(ptr nonnull @"revng.const.0x400000:Code_x86_64", i64 2, i32 1, i32 0, ptr null)
  %v1 = load i64, ptr @_rdi, align 8
  %v2 = and i64 %v1, u0xffffffff
  store i64 %v2, ptr @_rax, align 8
  call void (ptr, i64, i32, i32, ptr, ...) @newpc(ptr nonnull @"revng.const.0x400002:Code_x86_64", i64 3, i32 0, i32 0, ptr null)
  %v3 = load i64, ptr @_rsi, align 8
  call void @helper_divb_AL(ptr nonnull inttoptr (i64 u0x27c0 to ptr), i64 %v3)
  store i1 false, ptr @cpu_loop_exiting, align 1
  call void (ptr, i64, i32, i32, ptr, ...) @newpc(ptr nonnull @"revng.const.0x400005:Code_x86_64", i64 1, i32 0, i32 0, ptr null)
  %v4 = load i64, ptr @_rsp, align 8
  %v5 = inttoptr i64 %v4 to ptr
  %v6 = load i64, ptr %v5, align 1
  %v7 = add i64 %v4, 8
  store i64 %v7, ptr @_rsp, align 8
  store i64 %v6, ptr @_rip, align 8
  br label %anypc,
```

The `mov eax, edi` becomes `load @_rdi` → `and` (zero-extend to 32-bit) → `store @_rax`.
The `div sil` becomes `call void @helper_divb_AL(env, i64 %v3)` where the env pointer is folded to a constant `inttoptr` and `%v3` is the value of `@_rsi`.
The `ret` pops the return address from `@_rsp` into `@_rip`.

#### Helpers in the `enforce-abi` artifact

At the `enforce-abi` stage, the *to-inline* module is linked.
The `inline-helpers` pass walks each isolated function, finds calls to functions in `section "revng_inline"`, and inlines them in a fixed-point loop.

```bash silent
$ revng artifact enforce-abi div-binary --model model.yml -o enforced.bc
```

Let's look at the isolated function.

```bash
$ revng opt -strip-debug -S enforced.bc \
    | sed -n "/^define.*@local_0x400000_Code_x86_64/,/^}/p" \
    | sed -n "1p; /and i64.*u0xffff$/,/helper_divb_AL.exit:/p" \
    | pretty
define i64 @local_0x400000_Code_x86_64(i64 %rdi_x86_64, i64 %rsi_x86_64) {
  %v1 = and i64 %v2, u0xffff
  %v3 = trunc i64 %v1 to i32
  %v4 = and i64 %v5, 255
  %v6 = trunc i64 %v4 to i32
  %v7 = icmp eq i32 %v6, 0
  br i1 %v7, label %v8, label %v9

v8:
  unreachable

v9:
  %v10 = udiv i32 %v3, %v6
  %v11 = icmp ugt i32 %v10, 255
  br i1 %v11, label %v12, label %v13

v12:
  unreachable

v13:
  %v14 = and i32 %v10, 255
  %v15 = urem i32 %v3, %v6
  %v16 = and i32 %v15, 255
  %v17 = load i64, ptr %_rax, align 8
  %v18 = and i64 %v17, u0xffffffffffff0000
  %v19 = shl i32 %v16, 8
  %v20 = zext i32 %v19 to i64
  %v21 = or i64 %v18, %v20
  %v22 = zext i32 %v14 to i64
  %v23 = or i64 %v21, %v22
  store i64 %v23, ptr %_rax, align 8
  br label %helper_divb_AL.exit

helper_divb_AL.exit:
```

The `call void @helper_divb_AL(...)` is gone — its body has been inlined.
Since `remove-exceptional-functions` is part of the `enforce-abi` pipeline, the `raise_exception_ra` calls (which are `REVNG_EXCEPTIONAL`) have already been replaced with `unreachable`.

Compare this with the C source: the `udiv`/`urem` implement the division, `%_rax` is the accumulator, and the two `unreachable` blocks (labels `v8` and `v12`) are where `raise_exception_ra` used to be (division-by-zero and quotient-overflow checks).

Running `-simplifycfg` eliminates the `unreachable` blocks, turning the error conditions into `llvm.assume` intrinsics.
These `llvm.assume` calls are later removed by the `remove-llvmassume-calls` pass (which runs as part of the `legacy-segregate-stack-accesses` step).
Adding `-dce` cleans up the remaining dead instructions:

```bash
$ revng opt -strip-debug -simplifycfg -remove-llvmassume-calls -dce -S enforced.bc \
    | sed -n "/^define.*@local_0x400000_Code_x86_64/,/^}/p" \
    | sed -n "1p; /and i64.*u0xffff$/,/store i64.*%_rax/p" \
    | pretty
define i64 @local_0x400000_Code_x86_64(i64 %rdi_x86_64, i64 %rsi_x86_64) {
  %v1 = and i64 %v2, u0xffff
  %v3 = trunc i64 %v1 to i32
  %v4 = and i64 %v5, 255
  %v6 = trunc i64 %v4 to i32
  %v7 = udiv i32 %v3, %v6
  %v8 = and i32 %v7, 255
  %v9 = urem i32 %v3, %v6
  %v10 = and i32 %v9, 255
  %v11 = load i64, ptr %_rax, align 8
  %v12 = and i64 %v11, u0xffffffffffff0000
  %v13 = shl i32 %v10, 8
  %v14 = zext i32 %v13 to i64
  %v15 = or i64 %v12, %v14
  %v16 = zext i32 %v8 to i64
  %v17 = or i64 %v15, %v16
  store i64 %v17, ptr %_rax, align 8
```

The exceptional calls and dead code are completely gone.
What remains is a clean straight-line byte division: load RAX, divide, store quotient and remainder back into RAX.

#### Helpers in the `recompile` artifact

At recompile time, the *full* module is linked in.
Since the recompiler produces native code for *all* helper calls (including non-inline ones), it needs every helper definition — hence the large (~53 MB) *full* module.
