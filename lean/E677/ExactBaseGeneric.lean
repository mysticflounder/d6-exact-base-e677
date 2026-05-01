import E677.D6CoreMinimal

/-!
# Generic exact-base local lemma

This file tests whether the short d=6 exact-base proof is actually local in the
row data rather than intrinsically d=6.  The context below keeps only the rows
used by the final exact-base chain.
-/

universe u

variable {α : Type u} [Magma' α] [Fintype α]

structure ExactBaseLocalContext (α : Type u) [Magma' α] [Fintype α] where
  hE : E677 α
  x : α
  c1 : α
  c3 : α
  c4 : α
  A : α
  hL0 : x ◇ x = c1
  hL3 : x ◇ c3 = c4
  hc1x : c1 ◇ x = c4
  hA_Ax_eq_A : A ◇ (A ◇ x) = A
  hAA : A ◇ A = c1
  hA0 : A ◇ x = c3
  hT1 : c3 ◇ c3 = c1

namespace ExactBaseLocalContext

set_option linter.unusedFintypeInType false

theorem c3_mul_c1_eq_x (C : ExactBaseLocalContext α) :
    C.c3 ◇ C.c1 = C.x := by
  rcases C with ⟨h, x, c1, c3, c4, A, hL0, hL3, hc1x, hA_Ax, hAA, hA0, hT1⟩
  have hA3 : A ◇ c3 = A := by
    rw [← hA0]
    exact hA_Ax
  have htmp : A ◇ (c3 ◇ c1) = c3 := by
    simpa [hA3, hAA] using (h c3 A).symm
  exact d6_e677_left_cancel h A (htmp.trans hA0.symm)

theorem c1_mul_c4_eq_c3 (C : ExactBaseLocalContext α) :
    C.c1 ◇ C.c4 = C.c3 := by
  rcases C with ⟨h, x, c1, c3, c4, A, hL0, hL3, hc1x, hA_Ax, hAA, hA0, hT1⟩
  let C' : ExactBaseLocalContext α :=
    ⟨h, x, c1, c3, c4, A, hL0, hL3, hc1x, hA_Ax, hAA, hA0, hT1⟩
  have hc3c1 : c3 ◇ c1 = x := c3_mul_c1_eq_x C'
  have hEq : c1 = c3 ◇ (c1 ◇ c4) := by
    calc
      c1 = c3 ◇ (c1 ◇ ((c3 ◇ c1) ◇ c3)) := by simpa using (h c1 c3)
      _ = c3 ◇ (c1 ◇ (x ◇ c3)) := by rw [hc3c1]
      _ = c3 ◇ (c1 ◇ c4) := by rw [hL3]
  apply d6_e677_left_cancel h c3
  calc
    c3 ◇ (c1 ◇ c4) = c1 := hEq.symm
    _ = c3 ◇ c3 := hT1.symm

theorem c4_mul_x_eq_x (C : ExactBaseLocalContext α) :
    C.c4 ◇ C.x = C.x := by
  rcases C with ⟨h, x, c1, c3, c4, A, hL0, hL3, hc1x, hA_Ax, hAA, hA0, hT1⟩
  let C' : ExactBaseLocalContext α :=
    ⟨h, x, c1, c3, c4, A, hL0, hL3, hc1x, hA_Ax, hAA, hA0, hT1⟩
  have hc3c1 : c3 ◇ c1 = x := c3_mul_c1_eq_x C'
  have hc1c4 : c1 ◇ c4 = c3 := c1_mul_c4_eq_c3 C'
  have hEq : c4 = c1 ◇ (c4 ◇ x) := by
    calc
      c4 = c1 ◇ (c4 ◇ ((c1 ◇ c4) ◇ c1)) := by simpa using (h c4 c1)
      _ = c1 ◇ (c4 ◇ (c3 ◇ c1)) := by rw [hc1c4]
      _ = c1 ◇ (c4 ◇ x) := by rw [hc3c1]
  apply d6_e677_left_cancel h c1
  calc
    c1 ◇ (c4 ◇ x) = c4 := hEq.symm
    _ = c1 ◇ x := hc1x.symm

theorem fixer (C : ExactBaseLocalContext α) :
    ((C.x ◇ C.x) ◇ C.x) ◇ C.x = C.x := by
  rcases C with ⟨h, x, c1, c3, c4, A, hL0, hL3, hc1x, hA_Ax, hAA, hA0, hT1⟩
  let C' : ExactBaseLocalContext α :=
    ⟨h, x, c1, c3, c4, A, hL0, hL3, hc1x, hA_Ax, hAA, hA0, hT1⟩
  calc
    ((x ◇ x) ◇ x) ◇ x = (c1 ◇ x) ◇ x := by rw [hL0]
    _ = c4 ◇ x := by rw [hc1x]
    _ = x := c4_mul_x_eq_x C'

end ExactBaseLocalContext

/-!
## Indexed exact-base triple

The d=6 exact-base packet is the special case `ci = c1`, `cj = c3`,
`cnext = c4`.  The row-local proof only needs the connector
`ci ◇ x = cnext`, where `cnext = x ◇ cj`.
-/

structure ExactTripleLocalContext (α : Type u) [Magma' α] [Fintype α] where
  hE : E677 α
  x : α
  ci : α
  cj : α
  cnext : α
  A : α
  hxj : x ◇ cj = cnext
  hix : ci ◇ x = cnext
  hA_Ax_eq_A : A ◇ (A ◇ x) = A
  hAA : A ◇ A = ci
  hA0 : A ◇ x = cj
  hT : cj ◇ cj = ci

namespace ExactTripleLocalContext

set_option linter.unusedFintypeInType false

theorem cj_mul_ci_eq_x (C : ExactTripleLocalContext α) :
    C.cj ◇ C.ci = C.x := by
  rcases C with ⟨h, x, ci, cj, cnext, A, hxj, hix, hA_Ax, hAA, hA0, hT⟩
  have hAj : A ◇ cj = A := by
    rw [← hA0]
    exact hA_Ax
  have htmp : A ◇ (cj ◇ ci) = cj := by
    simpa [hAj, hAA] using (h cj A).symm
  exact d6_e677_left_cancel h A (htmp.trans hA0.symm)

theorem ci_mul_cnext_eq_cj (C : ExactTripleLocalContext α) :
    C.ci ◇ C.cnext = C.cj := by
  rcases C with ⟨h, x, ci, cj, cnext, A, hxj, hix, hA_Ax, hAA, hA0, hT⟩
  let C' : ExactTripleLocalContext α :=
    ⟨h, x, ci, cj, cnext, A, hxj, hix, hA_Ax, hAA, hA0, hT⟩
  have hcjci : cj ◇ ci = x := cj_mul_ci_eq_x C'
  have hEq : ci = cj ◇ (ci ◇ cnext) := by
    calc
      ci = cj ◇ (ci ◇ ((cj ◇ ci) ◇ cj)) := by simpa using (h ci cj)
      _ = cj ◇ (ci ◇ (x ◇ cj)) := by rw [hcjci]
      _ = cj ◇ (ci ◇ cnext) := by rw [hxj]
  apply d6_e677_left_cancel h cj
  calc
    cj ◇ (ci ◇ cnext) = ci := hEq.symm
    _ = cj ◇ cj := hT.symm

theorem cnext_mul_x_eq_x (C : ExactTripleLocalContext α) :
    C.cnext ◇ C.x = C.x := by
  rcases C with ⟨h, x, ci, cj, cnext, A, hxj, hix, hA_Ax, hAA, hA0, hT⟩
  let C' : ExactTripleLocalContext α :=
    ⟨h, x, ci, cj, cnext, A, hxj, hix, hA_Ax, hAA, hA0, hT⟩
  have hcjci : cj ◇ ci = x := cj_mul_ci_eq_x C'
  have hcicnext : ci ◇ cnext = cj := ci_mul_cnext_eq_cj C'
  have hEq : cnext = ci ◇ (cnext ◇ x) := by
    calc
      cnext = ci ◇ (cnext ◇ ((ci ◇ cnext) ◇ ci)) := by simpa using (h cnext ci)
      _ = ci ◇ (cnext ◇ (cj ◇ ci)) := by rw [hcicnext]
      _ = ci ◇ (cnext ◇ x) := by rw [hcjci]
  apply d6_e677_left_cancel h ci
  calc
    ci ◇ (cnext ◇ x) = cnext := hEq.symm
    _ = ci ◇ x := hix.symm

end ExactTripleLocalContext

/-!
## Exact spine

The first cancellation step does not need the square row `cj ◇ cj = ci` or the
connector row.  The shared spine

```text
A ◇ A = ci
A ◇ x = cj
A ◇ cj = A
```

already forces both `cj ◇ ci = x` and `ci ◇ A = x`.
-/

structure ExactSpineLocalContext (α : Type u) [Magma' α] [Fintype α] where
  hE : E677 α
  x : α
  ci : α
  cj : α
  A : α
  hAA : A ◇ A = ci
  hA0 : A ◇ x = cj
  hAj : A ◇ cj = A

namespace ExactSpineLocalContext

set_option linter.unusedFintypeInType false

theorem cj_mul_ci_eq_x (C : ExactSpineLocalContext α) :
    C.cj ◇ C.ci = C.x := by
  rcases C with ⟨h, x, ci, cj, A, hAA, hA0, hAj⟩
  have htmp : A ◇ (cj ◇ ci) = cj := by
    simpa [hAj, hAA] using (h cj A).symm
  exact d6_e677_left_cancel h A (htmp.trans hA0.symm)

theorem ci_mul_A_eq_x (C : ExactSpineLocalContext α) :
    C.ci ◇ C.A = C.x := by
  rcases C with ⟨h, x, ci, cj, A, hAA, hA0, hAj⟩
  have hEAA : A = A ◇ (A ◇ (ci ◇ A)) := by
    simpa [hAA] using h A A
  have hAciA : A ◇ (ci ◇ A) = cj := by
    apply d6_e677_left_cancel h A
    calc
      A ◇ (A ◇ (ci ◇ A)) = A := hEAA.symm
      _ = A ◇ cj := hAj.symm
  apply d6_e677_left_cancel h A
  calc
    A ◇ (ci ◇ A) = cj := hAciA
    _ = A ◇ x := hA0.symm

theorem ci_mul_A_eq_cj_mul_ci (C : ExactSpineLocalContext α) :
    C.ci ◇ C.A = C.cj ◇ C.ci := by
  rw [ci_mul_A_eq_x C, cj_mul_ci_eq_x C]

end ExactSpineLocalContext

/-!
## d=8 motif candidate

DB mining at d=8, gap=1 finds the uniform local motif:

```text
A ◇ A = c4
A ◇ x = c7
A ◇ c7 = A
c7 ◇ c7 = c7
c7 ◇ c4 = x
c4 ◇ x = c2
c4 ◇ c7 = c4
c7 ◇ A = c2
A ◇ c4 = c6
c4 ◇ A = x
```

The first useful local closure is `c7 ◇ c4 = x`, which is also visible in the
DB motif and follows by the same first cancellation step as the exact-triple
lemma, without assuming `c7 ◇ c7 = c4`.
-/

structure D8MotifLocalContext (α : Type u) [Magma' α] [Fintype α] where
  hE : E677 α
  x : α
  c2 : α
  c4 : α
  c6 : α
  c7 : α
  A : α
  hAA : A ◇ A = c4
  hA0 : A ◇ x = c7
  hA7 : A ◇ c7 = A
  h77 : c7 ◇ c7 = c7
  h4x : c4 ◇ x = c2
  h47 : c4 ◇ c7 = c4
  h7A : c7 ◇ A = c2
  hA4 : A ◇ c4 = c6
  h4A : c4 ◇ A = x

namespace D8MotifLocalContext

set_option linter.unusedFintypeInType false

/-- The d=8 motif contains the generic exact spine with `ci=c4`, `cj=c7`. -/
def toExactSpineLocalContext (C : D8MotifLocalContext α) :
    ExactSpineLocalContext α where
  hE := C.hE
  x := C.x
  ci := C.c4
  cj := C.c7
  A := C.A
  hAA := C.hAA
  hA0 := C.hA0
  hAj := C.hA7

/-- The first exact-triple-style cancellation still gives `c7 ◇ c4 = x`. -/
theorem c7_mul_c4_eq_x (C : D8MotifLocalContext α) :
    C.c7 ◇ C.c4 = C.x := by
  exact ExactSpineLocalContext.cj_mul_ci_eq_x C.toExactSpineLocalContext

/-- The same spine also gives `c4 ◇ A = x`; this was a DB motif row. -/
theorem c4_mul_A_eq_x (C : D8MotifLocalContext α) :
    C.c4 ◇ C.A = C.x :=
  ExactSpineLocalContext.ci_mul_A_eq_x C.toExactSpineLocalContext

/-- Transport-looking equality exposed by the d=8 motif spine. -/
theorem c4_mul_A_eq_c7_mul_c4 (C : D8MotifLocalContext α) :
    C.c4 ◇ C.A = C.c7 ◇ C.c4 :=
  ExactSpineLocalContext.ci_mul_A_eq_cj_mul_ci C.toExactSpineLocalContext

/-- Second transport-looking DB equality: `c7 ◇ A` and `c4 ◇ x` have the same value. -/
theorem c7_mul_A_eq_c4_mul_x (C : D8MotifLocalContext α) :
    C.c7 ◇ C.A = C.c4 ◇ C.x := by
  rw [C.h7A, C.h4x]

end D8MotifLocalContext
