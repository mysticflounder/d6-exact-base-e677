import E677.D6Isolated
import E677.ExactBaseGeneric

/-!
# Publication-facing d=6 exact-base surface

This file is intentionally small and imports only the Core-based isolated d=6
context.  It provides stable names for the d=6 exact-base row and fixer theorem
without depending on the large gap-1 dispatcher or its closeout wrapper types.
-/

universe u

namespace D6Gap1Context

variable {α : Type u} [Magma' α] [Fintype α]

/-- Convert the d=6 exact-base packet rows to the generic local exact-base context. -/
def toExactBaseLocalContext
    (C : D6Gap1Context α)
    (hAA : C.A ◇ C.A = C.c1)
    (hA0 : C.A ◇ C.x = C.c3)
    (hT1 : C.c3 ◇ C.c3 = C.c1) :
    ExactBaseLocalContext α where
  hE := C.hE
  x := C.x
  c1 := C.c1
  c3 := C.c3
  c4 := C.c4
  A := C.A
  hL0 := C.hL0
  hL3 := C.hL3
  hc1x := C.c1_mul_x_eq_c4
  hA_Ax_eq_A := C.hA_Ax_eq_A
  hAA := hAA
  hA0 := hA0
  hT1 := hT1

/-- Publication-facing statement for the exact-base row: `c4` fixes `x`. -/
theorem publication_exact_base_c4_mul_x_eq_x
    (C : D6Gap1Context α)
    (hAA : C.A ◇ C.A = C.c1)
    (hA0 : C.A ◇ C.x = C.c3)
    (hT1 : C.c3 ◇ C.c3 = C.c1) :
    C.c4 ◇ C.x = C.x :=
  ExactBaseLocalContext.c4_mul_x_eq_x (C.toExactBaseLocalContext hAA hA0 hT1)

/-- Publication-facing d=6 exact-base fixer theorem. -/
theorem publication_exact_base_fixer
    (C : D6Gap1Context α)
    (hAA : C.A ◇ C.A = C.c1)
    (hA0 : C.A ◇ C.x = C.c3)
    (hT1 : C.c3 ◇ C.c3 = C.c1) :
    ((C.x ◇ C.x) ◇ C.x) ◇ C.x = C.x :=
  ExactBaseLocalContext.fixer (C.toExactBaseLocalContext hAA hA0 hT1)

end D6Gap1Context

/--
Publication packet for the exact-base d=6 branch.

The large branch context remains in `ctx`, but the theorem-facing API now has a
single object carrying exactly the three additional exact-base rows used by the
isolated proof.
-/
structure D6ExactBasePacket (α : Type u) [Magma' α] [Fintype α] where
  ctx : D6Gap1Context α
  hAA : ctx.A ◇ ctx.A = ctx.c1
  hA0 : ctx.A ◇ ctx.x = ctx.c3
  hT1 : ctx.c3 ◇ ctx.c3 = ctx.c1

namespace D6ExactBasePacket

variable {α : Type u} [Magma' α] [Fintype α]

/-- Exact-base row exported through the compact publication packet. -/
theorem c4_mul_x_eq_x (P : D6ExactBasePacket α) :
    P.ctx.c4 ◇ P.ctx.x = P.ctx.x :=
  P.ctx.publication_exact_base_c4_mul_x_eq_x P.hAA P.hA0 P.hT1

/-- Exact-base d=6 fixer theorem exported through the compact publication packet. -/
theorem fixer (P : D6ExactBasePacket α) :
    ((P.ctx.x ◇ P.ctx.x) ◇ P.ctx.x) ◇ P.ctx.x = P.ctx.x :=
  P.ctx.publication_exact_base_fixer P.hAA P.hA0 P.hT1

end D6ExactBasePacket
