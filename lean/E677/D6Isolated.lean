import E677.D6CoreMinimal

/-!
# Isolated d=6 packet layer

This file is the start of the writeup-oriented d=6 extraction.  It deliberately
does not import `E677.Gap1`, `E677.DratBridgeGap1`, `E677.TransportBridgeGap1`,
or any generated certificate file.

The local proof is stated over `D6Gap1Context`: a small finite d=6 capsule that
contains the seven-value cover, the `L_x` row, and only the gap-1 consequences
actually consumed by the local d=6 packet proofs.
-/

universe u

variable {α : Type u} [Magma' α] [Fintype α]

structure D6Gap1Context (α : Type u) [Magma' α] [Fintype α] where
  hE : E677 α
  x : α
  c1 : α
  c2 : α
  c3 : α
  c4 : α
  c5 : α
  A : α
  hA_notin : ∀ n : ℕ, A ≠ (fun z => x ◇ z)^[n] x
  hOrbit_mul_A_ne_A :
    ∀ {y : α}, (∃ k : ℕ, y = (fun z => x ◇ z)^[k] x) → y ≠ x → y ◇ A ≠ A
  hcover : ∀ a : α, a = x ∨ a = c1 ∨ a = c2 ∨ a = c3 ∨
    a = c4 ∨ a = c5 ∨ a = A
  hL0 : x ◇ x = c1
  hL1 : x ◇ c1 = c2
  hL2 : x ◇ c2 = c3
  hL3 : x ◇ c3 = c4
  hL4 : x ◇ c4 = c5
  hL5 : x ◇ c5 = x
  h02 : x ≠ c2
  h25 : c2 ≠ c5
  hLA : x ◇ A = A
  hA_Ax_eq_A : A ◇ (A ◇ x) = A
  hPhi : (A ◇ A) ◇ A = x
  hAxAA : (A ◇ x) ◇ (A ◇ A) = x

namespace D6Gap1Context

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

theorem c5_mul_c1_eq_c4 (C : D6Gap1Context α) :
    C.c5 ◇ C.c1 = C.c4 := by
  rcases C with
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  apply d6_e677_left_cancel h x
  calc
    x ◇ (c5 ◇ c1) = c5 := by
      simpa [hL5, hL0] using (h c5 x).symm
    _ = x ◇ c4 := hL4.symm

theorem c1_mul_x_eq_c4 (C : D6Gap1Context α) :
    C.c1 ◇ C.x = C.c4 := by
  rcases C with
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  have h01 : x ≠ c1 := by
    intro h01
    have hxx : x ◇ x = x := by simpa [h01] using hL0
    have hx2 : x = c2 := by
      calc
        x = x ◇ x := hxx.symm
        _ = x ◇ c1 := by rw [h01]
        _ = c2 := hL1
    exact h02 hx2
  have h03 : x ≠ c3 := by
    intro h03
    have h14 : c1 = c4 := by
      calc
        c1 = x ◇ x := hL0.symm
        _ = x ◇ c3 := by rw [h03]
        _ = c4 := hL3
    have hc25 : c2 = c5 := by
      calc
        c2 = x ◇ c1 := hL1.symm
        _ = x ◇ c4 := by rw [h14]
        _ = c5 := hL4
    exact h25 hc25
  have h04 : x ≠ c4 := by
    intro h04
    have hx2 : x = c2 := by
      have hc51 : c5 = c1 := by
        calc
          c5 = x ◇ c4 := hL4.symm
          _ = x ◇ x := by rw [h04]
          _ = c1 := hL0
      calc
        x = x ◇ c5 := hL5.symm
        _ = x ◇ c1 := by rw [hc51]
        _ = c2 := hL1
    exact h02 hx2
  have h05 : x ≠ c5 := by
    intro h05
    have hxx : x ◇ x = x := by simpa [h05] using hL5
    have hx1 : x = c1 := hxx.symm.trans hL0
    have hx2 : x = c2 := by
      calc
        x = x ◇ x := hxx.symm
        _ = x ◇ c1 := by rw [hx1]
        _ = c2 := hL1
    exact h02 hx2
  rcases hcover (c1 ◇ x) with
    h1x | h1x | h1x | h1x | h1x | h1x | h1x
  · exfalso
    have hx2 : x = c2 := by
      calc
        x = x ◇ (x ◇ ((x ◇ x) ◇ x)) := h x x
        _ = x ◇ c1 := by rw [hL0, h1x, hL0]
        _ = c2 := hL1
    exact h02 hx2
  · exfalso
    have hx3 : x = c3 := by
      calc
        x = x ◇ (x ◇ ((x ◇ x) ◇ x)) := h x x
        _ = x ◇ (x ◇ c1) := by rw [hL0, h1x]
        _ = x ◇ c2 := by rw [hL1]
        _ = c3 := hL2
    exact h03 hx3
  · exfalso
    have hx4 : x = c4 := by
      calc
        x = x ◇ (x ◇ ((x ◇ x) ◇ x)) := h x x
        _ = x ◇ (x ◇ c2) := by rw [hL0, h1x]
        _ = x ◇ c3 := by rw [hL2]
        _ = c4 := hL3
    exact h04 hx4
  · exfalso
    have hx5 : x = c5 := by
      calc
        x = x ◇ (x ◇ ((x ◇ x) ◇ x)) := h x x
        _ = x ◇ (x ◇ c3) := by rw [hL0, h1x]
        _ = x ◇ c4 := by rw [hL3]
        _ = c5 := hL4
    exact h05 hx5
  · exact h1x
  · exfalso
    have hx1 : x = c1 := by
      calc
        x = x ◇ (x ◇ ((x ◇ x) ◇ x)) := h x x
        _ = x ◇ (x ◇ c5) := by rw [hL0, h1x]
        _ = x ◇ x := by rw [hL5]
        _ = c1 := hL0
    exact h01 hx1
  · exfalso
    have hxA : x = A := by
      calc
        x = x ◇ (x ◇ ((x ◇ x) ◇ x)) := h x x
        _ = x ◇ (x ◇ A) := by rw [hL0, h1x]
        _ = A := by simp [hLA]
    exact hA_notin 0 hxA.symm

theorem c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_c5c3_eq_A
    (C : D6Gap1Context α)
    (hAA : C.A ◇ C.A = C.c5)
    (hA0 : C.A ◇ C.x = C.c3) :
    C.c5 ◇ C.c3 = C.A := by
  rcases C with
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  change A ◇ A = c5 at hAA
  change A ◇ x = c3 at hA0
  have h5A0 : c5 ◇ A = x := by
    rw [← hAA]
    exact hPhi
  have htmp : A = c5 ◇ c3 := by
    calc
      A = c5 ◇ (A ◇ ((c5 ◇ A) ◇ c5)) := h A c5
      _ = c5 ◇ (A ◇ (x ◇ c5)) := by rw [h5A0]
      _ = c5 ◇ (A ◇ x) := by rw [hL5]
      _ = c5 ◇ c3 := by rw [hA0]
  exact htmp.symm

theorem c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_c3A_eq_c1
    (C : D6Gap1Context α)
    (h1A5 : C.c1 ◇ C.A = C.c5)
    (hAA : C.A ◇ C.A = C.c5)
    (hA0 : C.A ◇ C.x = C.c3) :
    C.c3 ◇ C.A = C.c1 := by
  rcases C with
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  change c1 ◇ A = c5 at h1A5
  change A ◇ A = c5 at hAA
  change A ◇ x = c3 at hA0
  let C' : D6Gap1Context α :=
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  have hA3 : A ◇ c3 = A := by
    rw [← hA0]
    exact hA_Ax
  have h5A0 : c5 ◇ A = x := by
    rw [← hAA]
    exact hPhi
  have h3c5 : c3 ◇ c5 = x := by
    have htmp : A ◇ (c3 ◇ c5) = c3 := by
      simpa [hA3, hAA] using (h c3 A).symm
    exact d6_e677_left_cancel h A (htmp.trans hA0.symm)
  have h03 : x ≠ c3 := by
    intro h03
    have h25eq : c2 = c5 := d6_e677_left_cancel h x (by
      calc
        x ◇ c2 = x := by simpa [h03] using hL2
        _ = x ◇ c5 := hL5.symm)
    exact h25 h25eq
  have h04 : x ≠ c4 := by
    intro h04
    have h15eq : c1 = c5 := by
      calc
        c1 = x ◇ x := hL0.symm
        _ = x ◇ c4 := by rw [h04]
        _ = c5 := hL4
    have h2x : c2 = x := by
      calc
        c2 = x ◇ c1 := hL1.symm
        _ = x ◇ c5 := by rw [h15eq]
        _ = x := hL5
    exact h02 h2x.symm
  have h35 : c3 ≠ c5 := by
    intro h35
    have h4x : c4 = x := by
      calc
        c4 = x ◇ c3 := hL3.symm
        _ = x ◇ c5 := by rw [h35]
        _ = x := hL5
    exact h04 h4x.symm
  have h4A_ne : c4 ≠ A := by
    have hc4_orbit_eq : (fun z => x ◇ z)^[4] x = c4 := by
      simp [Function.iterate_succ_apply', hL0, hL1, hL2, hL3]
    intro h4A
    exact hA_notin 4 (h4A.symm.trans hc4_orbit_eq.symm)
  have h5A_ne : c5 ≠ A := by
    have hc5_orbit_eq : (fun z => x ◇ z)^[5] x = c5 := by
      simp [Function.iterate_succ_apply', hL0, hL1, hL2, hL3, hL4]
    intro h5A
    exact hA_notin 5 (h5A.symm.trans hc5_orbit_eq.symm)
  have hc3_orbit : ∃ k : ℕ, c3 = (fun z => x ◇ z)^[k] x := by
    refine ⟨3, ?_⟩
    change c3 = x ◇ (x ◇ (x ◇ x))
    rw [hL0, hL1]
    exact hL2.symm
  have h3A_ne_A : c3 ◇ A ≠ A :=
    hOrbitA hc3_orbit h03.symm
  have h5c1 : c5 ◇ c1 = c4 := c5_mul_c1_eq_c4 C'
  have h1x4 : c1 ◇ x = c4 := c1_mul_x_eq_c4 C'
  have hEA : A ◇ (x ◇ (c3 ◇ A)) = x := by
    simpa [hA0] using (h x A).symm
  rcases hcover (c3 ◇ A) with h3A | h3A | h3A | h3A | h3A | h3A | h3A
  · exfalso
    have hAeq5 : A = c5 := d6_e677_left_cancel h c3 (h3A.trans h3c5.symm)
    exact h5A_ne hAeq5.symm
  · exact h3A
  · exfalso
    have hA3x : A ◇ c3 = x := by simpa [h3A, hL2] using hEA
    have hAx : A = x := hA3.symm.trans hA3x
    exact hA_notin 0 hAx
  · exfalso
    have hA4x : A ◇ c4 = x := by simpa [h3A, hL3] using hEA
    have h1xA : c1 ◇ x = A := by
      simpa [h1A5, h5c1, hA4x] using (h A c1).symm
    have h4Aeq : c4 = A := h1x4.symm.trans h1xA
    exact h4A_ne h4Aeq
  · exfalso
    have hA5x : A ◇ c5 = x := by simpa [h3A, hL4] using hEA
    have hA0eq5 : A ◇ x = c5 := by
      simpa [hA5x, hLA, h5A0] using (h c5 A).symm
    have h35eq : c3 = c5 := hA0.symm.trans hA0eq5
    exact h35 h35eq
  · exfalso
    have hA0x : A ◇ x = x := by simpa [h3A, hL5] using hEA
    have h3x : c3 = x := hA0.symm.trans hA0x
    exact h03 h3x.symm
  · exfalso
    exact h3A_ne_A h3A

theorem c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_Ac2_eq_x
    (C : D6Gap1Context α)
    (hA0 : C.A ◇ C.x = C.c3)
    (h3A1 : C.c3 ◇ C.A = C.c1) :
    C.A ◇ C.c2 = C.x := by
  rcases C with
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  change A ◇ x = c3 at hA0
  change c3 ◇ A = c1 at h3A1
  have hEA : A ◇ (x ◇ (c3 ◇ A)) = x := by
    simpa [hA0] using (h x A).symm
  simpa [h3A1, hL1] using hEA

theorem c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_Ac5_eq_c4
    (C : D6Gap1Context α)
    (h1A5 : C.c1 ◇ C.A = C.c5)
    (hAA : C.A ◇ C.A = C.c5)
    (hA0 : C.A ◇ C.x = C.c3) :
    C.A ◇ C.c5 = C.c4 := by
  rcases C with
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  change c1 ◇ A = c5 at h1A5
  change A ◇ A = c5 at hAA
  change A ◇ x = c3 at hA0
  let C' : D6Gap1Context α :=
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  have hA3 : A ◇ c3 = A := by
    rw [← hA0]
    exact hA_Ax
  have h5A0 : c5 ◇ A = x := by
    rw [← hAA]
    exact hPhi
  have h3A1 : c3 ◇ A = c1 :=
    c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_c3A_eq_c1 C' h1A5 hAA hA0
  have h5c3 : c5 ◇ c3 = A :=
    c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_c5c3_eq_A C' hAA hA0
  have hA2 : A ◇ c2 = x :=
    c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_Ac2_eq_x C' hA0 h3A1
  have h03 : x ≠ c3 := by
    intro h03
    have h25eq : c2 = c5 := d6_e677_left_cancel h x (by
      calc
        x ◇ c2 = x := by simpa [h03] using hL2
        _ = x ◇ c5 := hL5.symm)
    exact h25 h25eq
  have h05 : x ≠ c5 := by
    intro h05
    have h1x : c1 = x := by
      calc
        c1 = x ◇ x := hL0.symm
        _ = x ◇ c5 := by rw [h05]
        _ = x := hL5
    have h2x : c2 = x := by
      calc
        c2 = x ◇ c1 := hL1.symm
        _ = x ◇ x := by rw [h1x]
        _ = c1 := hL0
        _ = x := h1x
    exact h02 h2x.symm
  have h35 : c3 ≠ c5 := by
    intro h35
    have h4x : c4 = x := by
      calc
        c4 = x ◇ c3 := hL3.symm
        _ = x ◇ c5 := by rw [h35]
        _ = x := hL5
    have h15 : c1 = c5 := by
      calc
        c1 = x ◇ x := hL0.symm
        _ = x ◇ c4 := by rw [h4x]
        _ = c5 := hL4
    have h2x : c2 = x := by
      calc
        c2 = x ◇ c1 := hL1.symm
        _ = x ◇ c5 := by rw [h15]
        _ = x := hL5
    exact h02 h2x.symm
  have h2A_ne : c2 ≠ A := by
    have hc2_orbit_eq : (fun z => x ◇ z)^[2] x = c2 := by
      simp [Function.iterate_succ_apply', hL0, hL1]
    intro h2Aeq
    exact hA_notin 2 (h2Aeq.symm.trans hc2_orbit_eq.symm)
  have h5A_ne : c5 ≠ A := by
    have hc5_orbit_eq : (fun z => x ◇ z)^[5] x = c5 := by
      simp [Function.iterate_succ_apply', hL0, hL1, hL2, hL3, hL4]
    intro h5A
    exact hA_notin 5 (h5A.symm.trans hc5_orbit_eq.symm)
  have hback : A = c5 ◇ ((A ◇ c5) ◇ A) := by
    simpa [hAA] using (d6_e677_backward_recurrence h A A)
  rcases hcover (A ◇ c5) with hA5 | hA5 | hA5 | hA5 | hA5 | hA5 | hA5
  · exfalso
    have hAx : A = x := by
      calc
        A = c5 ◇ ((A ◇ c5) ◇ A) := hback
        _ = c5 ◇ (x ◇ A) := by rw [hA5]
        _ = c5 ◇ A := by rw [hLA]
        _ = x := h5A0
    exact hA_notin 0 hAx
  · exfalso
    have h55 : c5 ◇ c5 = A := by
      calc
        c5 ◇ c5 = c5 ◇ ((A ◇ c5) ◇ A) := by rw [hA5, h1A5]
        _ = A := hback.symm
    have h53 : c5 = c3 := d6_e677_left_cancel h c5 (h55.trans h5c3.symm)
    exact h35 h53.symm
  · exfalso
    have h2A3 : c2 ◇ A = c3 := by
      have htmp : c5 ◇ (c2 ◇ A) = A := by
        simpa [hA5] using hback.symm
      exact d6_e677_left_cancel h c5 (htmp.trans h5c3.symm)
    have h2eqA : c2 = A := by
      calc
        c2 = A ◇ (c2 ◇ ((A ◇ c2) ◇ A)) := h c2 A
        _ = A ◇ (c2 ◇ (x ◇ A)) := by rw [hA2]
        _ = A ◇ (c2 ◇ A) := by rw [hLA]
        _ = A ◇ c3 := by rw [h2A3]
        _ = A := hA3
    exact h2A_ne h2eqA
  · exfalso
    have h5x : c5 = x := d6_e677_left_cancel h A (hA5.trans hA0.symm)
    exact h05 h5x.symm
  · exact hA5
  · exfalso
    have h5Aeq : c5 = A := d6_e677_left_cancel h A (hA5.trans hAA.symm)
    exact h5A_ne h5Aeq
  · exfalso
    have h55 : c5 ◇ c5 = A := by
      calc
        c5 ◇ c5 = c5 ◇ ((A ◇ c5) ◇ A) := by rw [hA5, hAA]
        _ = A := hback.symm
    have h53 : c5 = c3 := d6_e677_left_cancel h c5 (h55.trans h5c3.symm)
    exact h35 h53.symm

theorem c5_branch_AA_eq_c5_and_Ax_eq_c3_and_Ac4_eq_c1_false
    (C : D6Gap1Context α)
    (h1A5 : C.c1 ◇ C.A = C.c5)
    (hAA : C.A ◇ C.A = C.c5)
    (hA0 : C.A ◇ C.x = C.c3)
    (hA4 : C.A ◇ C.c4 = C.c1) :
    False := by
  rcases C with
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  change c1 ◇ A = c5 at h1A5
  change A ◇ A = c5 at hAA
  change A ◇ x = c3 at hA0
  change A ◇ c4 = c1 at hA4
  let C' : D6Gap1Context α :=
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  have hA3 : A ◇ c3 = A := by
    rw [← hA0]
    exact hA_Ax
  have h3A1 : c3 ◇ A = c1 :=
    c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_c3A_eq_c1 C' h1A5 hAA hA0
  have hA2 : A ◇ c2 = x :=
    c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_Ac2_eq_x C' hA0 h3A1
  have hA5 : A ◇ c5 = c4 :=
    c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_Ac5_eq_c4 C' h1A5 hAA hA0
  have h1x4 : c1 ◇ x = c4 := c1_mul_x_eq_c4 C'
  have h01 : x ≠ c1 := by
    intro h01
    have h2x : c2 = x := by
      calc
        c2 = x ◇ c1 := hL1.symm
        _ = x ◇ x := by rw [h01.symm]
        _ = c1 := hL0
        _ = x := h01.symm
    exact h02 h2x.symm
  have h12 : c1 ≠ c2 := by
    intro h12
    have hx1 : x = c1 := d6_e677_left_cancel h x (hL0.trans (by simpa [h12.symm] using hL1.symm))
    exact h01 hx1
  have h13 : c1 ≠ c3 := by
    intro h13
    have h24 : c2 = c4 := by
      calc
        c2 = x ◇ c1 := hL1.symm
        _ = x ◇ c3 := by rw [h13]
        _ = c4 := hL3
    have h35 : c3 = c5 := by
      calc
        c3 = x ◇ c2 := hL2.symm
        _ = x ◇ c4 := by rw [h24]
        _ = c5 := hL4
    have h2x : c2 = x := by
      calc
        c2 = c4 := h24
        _ = x ◇ c3 := hL3.symm
        _ = x ◇ c5 := by rw [h35]
        _ = x := hL5
    exact h02 h2x.symm
  have h14 : c1 ≠ c4 := by
    intro h14
    have h25eq : c2 = c5 := by
      calc
        c2 = x ◇ c1 := hL1.symm
        _ = x ◇ c4 := by rw [h14]
        _ = c5 := hL4
    exact h25 h25eq
  have h15 : c1 ≠ c5 := by
    intro h15
    have h2x : c2 = x := by
      calc
        c2 = x ◇ c1 := hL1.symm
        _ = x ◇ c5 := by rw [h15]
        _ = x := hL5
    exact h02 h2x.symm
  have h1A : c1 ≠ A := by
    have hc1_orbit_eq : (fun z => x ◇ z)^[1] x = c1 := by
      simp [hL0]
    intro h1A
    exact hA_notin 1 (h1A.symm.trans hc1_orbit_eq.symm)
  have h23 : c2 ≠ c3 := by
    intro h23
    have h34 : c3 = c4 := by
      calc
        c3 = x ◇ c2 := hL2.symm
        _ = x ◇ c3 := by rw [h23]
        _ = c4 := hL3
    have h45 : c4 = c5 := by
      calc
        c4 = x ◇ c3 := hL3.symm
        _ = x ◇ c4 := by rw [h34]
        _ = c5 := hL4
    exact h25 (h23.trans (h34.trans h45))
  have h24 : c2 ≠ c4 := by
    intro h24
    have h35 : c3 = c5 := by
      calc
        c3 = x ◇ c2 := hL2.symm
        _ = x ◇ c4 := by rw [h24]
        _ = c5 := hL4
    have h2x : c2 = x := by
      calc
        c2 = c4 := h24
        _ = x ◇ c3 := hL3.symm
        _ = x ◇ c5 := by rw [h35]
        _ = x := hL5
    exact h02 h2x.symm
  have h2A_ne : c2 ≠ A := by
    have hc2_orbit_eq : (fun z => x ◇ z)^[2] x = c2 := by
      simp [Function.iterate_succ_apply', hL0, hL1]
    intro h2A
    exact hA_notin 2 (h2A.symm.trans hc2_orbit_eq.symm)
  have hA1 : A ◇ c1 = c2 := by
    rcases hcover (A ◇ c1) with hA1 | hA1 | hA1 | hA1 | hA1 | hA1 | hA1
    · have h12eq : c1 = c2 := d6_e677_left_cancel h A (hA1.trans hA2.symm)
      exact (h12 h12eq).elim
    · have h14eq : c1 = c4 := d6_e677_left_cancel h A (hA1.trans hA4.symm)
      exact (h14 h14eq).elim
    · exact hA1
    · have h1x : c1 = x := d6_e677_left_cancel h A (hA1.trans hA0.symm)
      exact (h01 h1x.symm).elim
    · have h15eq : c1 = c5 := d6_e677_left_cancel h A (hA1.trans hA5.symm)
      exact (h15 h15eq).elim
    · have h1Aeq : c1 = A := d6_e677_left_cancel h A (hA1.trans hAA.symm)
      exact (h1A h1Aeq).elim
    · have h13eq : c1 = c3 := d6_e677_left_cancel h A (hA1.trans hA3.symm)
      exact (h13 h13eq).elim
  have hc2_image : c2 = A ◇ (c2 ◇ A) := by
    calc
      c2 = A ◇ (c2 ◇ ((A ◇ c2) ◇ A)) := h c2 A
      _ = A ◇ (c2 ◇ (x ◇ A)) := by rw [hA2]
      _ = A ◇ (c2 ◇ A) := by rw [hLA]
  rcases hcover (c2 ◇ A) with h2A | h2A | h2A | h2A | h2A | h2A | h2A
  · have h23eq : c2 = c3 := by simpa [h2A, hA0] using hc2_image
    exact h23 h23eq
  · have h11 : c1 ◇ c1 = c4 := by
      have htmp : A ◇ (c1 ◇ c1) = c1 := by
        calc
          A ◇ (c1 ◇ c1) = A ◇ (c1 ◇ ((A ◇ c1) ◇ A)) := by rw [hA1, h2A]
          _ = c1 := by simpa using (h c1 A).symm
      exact d6_e677_left_cancel h A (htmp.trans hA4.symm)
    have h1x : c1 = x := d6_e677_left_cancel h c1 (h11.trans h1x4.symm)
    exact h01 h1x.symm
  · have h2x : c2 = x := by simpa [h2A, hA2] using hc2_image
    exact h02 h2x.symm
  · have h2Aeq : c2 = A := by simpa [h2A, hA3] using hc2_image
    exact h2A_ne h2Aeq
  · have h21 : c2 = c1 := by simpa [h2A, hA4] using hc2_image
    exact h12 h21.symm
  · have h24eq : c2 = c4 := by simpa [h2A, hA5] using hc2_image
    exact h24 h24eq
  · have h25eq : c2 = c5 := by simpa [h2A, hAA] using hc2_image
    exact h25 h25eq

theorem c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_Ac4_eq_c2
    (C : D6Gap1Context α)
    (h1A5 : C.c1 ◇ C.A = C.c5)
    (hAA : C.A ◇ C.A = C.c5)
    (hA0 : C.A ◇ C.x = C.c3) :
    C.A ◇ C.c4 = C.c2 := by
  rcases C with
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  change c1 ◇ A = c5 at h1A5
  change A ◇ A = c5 at hAA
  change A ◇ x = c3 at hA0
  let C' : D6Gap1Context α :=
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  have hA3 : A ◇ c3 = A := by
    rw [← hA0]
    exact hA_Ax
  have h3A1 : c3 ◇ A = c1 :=
    c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_c3A_eq_c1 C' h1A5 hAA hA0
  have hA2 : A ◇ c2 = x :=
    c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_Ac2_eq_x C' hA0 h3A1
  have hA5 : A ◇ c5 = c4 :=
    c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_Ac5_eq_c4 C' h1A5 hAA hA0
  have h04 : x ≠ c4 := by
    intro h04
    have h15 : c1 = c5 := by
      calc
        c1 = x ◇ x := hL0.symm
        _ = x ◇ c4 := by rw [h04]
        _ = c5 := hL4
    have h2x : c2 = x := by
      calc
        c2 = x ◇ c1 := hL1.symm
        _ = x ◇ c5 := by rw [h15]
        _ = x := hL5
    exact h02 h2x.symm
  have h05 : x ≠ c5 := by
    intro h05
    have h1x : c1 = x := by
      calc
        c1 = x ◇ x := hL0.symm
        _ = x ◇ c5 := by rw [h05]
        _ = x := hL5
    have h2x : c2 = x := by
      calc
        c2 = x ◇ c1 := hL1.symm
        _ = x ◇ x := by rw [h1x]
        _ = c1 := hL0
        _ = x := h1x
    exact h02 h2x.symm
  have h24 : c2 ≠ c4 := by
    intro h24
    have h35 : c3 = c5 := by
      calc
        c3 = x ◇ c2 := hL2.symm
        _ = x ◇ c4 := by rw [h24]
        _ = c5 := hL4
    have h2x : c2 = x := by
      calc
        c2 = c4 := h24
        _ = x ◇ c3 := hL3.symm
        _ = x ◇ c5 := by rw [h35]
        _ = x := hL5
    exact h02 h2x.symm
  have h34 : c3 ≠ c4 := by
    intro h34
    have h23 : c2 = c3 := d6_e677_left_cancel h x (hL2.trans (by simpa [h34] using hL3.symm))
    have h35 : c3 = c5 := by
      calc
        c3 = x ◇ c2 := hL2.symm
        _ = x ◇ c4 := by rw [h23, h34]
        _ = c5 := hL4
    exact h25 (h23.trans h35)
  have h45 : c4 ≠ c5 := by
    intro h45
    have h5x : c5 = x := by
      calc
        c5 = x ◇ c4 := hL4.symm
        _ = x ◇ c5 := by rw [h45]
        _ = x := hL5
    exact h05 h5x.symm
  have h4A : c4 ≠ A := by
    have hc4_orbit_eq : (fun z => x ◇ z)^[4] x = c4 := by
      simp [Function.iterate_succ_apply', hL0, hL1, hL2, hL3]
    intro h4A
    exact hA_notin 4 (h4A.symm.trans hc4_orbit_eq.symm)
  rcases hcover (A ◇ c4) with hA4 | hA4 | hA4 | hA4 | hA4 | hA4 | hA4
  · have h42 : c4 = c2 := d6_e677_left_cancel h A (hA4.trans hA2.symm)
    exact (h24 h42.symm).elim
  · exfalso
    exact c5_branch_AA_eq_c5_and_Ax_eq_c3_and_Ac4_eq_c1_false C' h1A5 hAA hA0 hA4
  · exact hA4
  · have h4x : c4 = x := d6_e677_left_cancel h A (hA4.trans hA0.symm)
    exact (h04 h4x.symm).elim
  · have h45eq : c4 = c5 := d6_e677_left_cancel h A (hA4.trans hA5.symm)
    exact (h45 h45eq).elim
  · have h4Aeq : c4 = A := d6_e677_left_cancel h A (hA4.trans hAA.symm)
    exact (h4A h4Aeq).elim
  · have h43 : c4 = c3 := d6_e677_left_cancel h A (hA4.trans hA3.symm)
    exact (h34 h43.symm).elim

theorem c5_branch_AA_eq_c5_and_Ax_eq_c3_and_Ac4_eq_c2_false
    (C : D6Gap1Context α)
    (h1A5 : C.c1 ◇ C.A = C.c5)
    (hAA : C.A ◇ C.A = C.c5)
    (hA0 : C.A ◇ C.x = C.c3)
    (hA4 : C.A ◇ C.c4 = C.c2) :
    False := by
  rcases C with
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  change c1 ◇ A = c5 at h1A5
  change A ◇ A = c5 at hAA
  change A ◇ x = c3 at hA0
  change A ◇ c4 = c2 at hA4
  let C' : D6Gap1Context α :=
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  have hA3 : A ◇ c3 = A := by
    rw [← hA0]
    exact hA_Ax
  have h3A1 : c3 ◇ A = c1 :=
    c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_c3A_eq_c1 C' h1A5 hAA hA0
  have hA2 : A ◇ c2 = x :=
    c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_Ac2_eq_x C' hA0 h3A1
  have hA5 : A ◇ c5 = c4 :=
    c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_Ac5_eq_c4 C' h1A5 hAA hA0
  have h5A0 : c5 ◇ A = x := by
    rw [← hAA]
    exact hPhi
  have h5c1 : c5 ◇ c1 = c4 := c5_mul_c1_eq_c4 C'
  have h1x4 : c1 ◇ x = c4 := c1_mul_x_eq_c4 C'
  have h01 : x ≠ c1 := by
    intro h01
    have h2x : c2 = x := by
      calc
        c2 = x ◇ c1 := hL1.symm
        _ = x ◇ x := by rw [h01.symm]
        _ = c1 := hL0
        _ = x := h01.symm
    exact h02 h2x.symm
  have h04 : x ≠ c4 := by
    intro h04
    have h15 : c1 = c5 := by
      calc
        c1 = x ◇ x := hL0.symm
        _ = x ◇ c4 := by rw [h04]
        _ = c5 := hL4
    have h2x : c2 = x := by
      calc
        c2 = x ◇ c1 := hL1.symm
        _ = x ◇ c5 := by rw [h15]
        _ = x := hL5
    exact h02 h2x.symm
  have h12 : c1 ≠ c2 := by
    intro h12
    have hx1 : x = c1 := d6_e677_left_cancel h x (hL0.trans (by simpa [h12.symm] using hL1.symm))
    exact h01 hx1
  have h13 : c1 ≠ c3 := by
    intro h13
    have h24eq : c2 = c4 := by
      calc
        c2 = x ◇ c1 := hL1.symm
        _ = x ◇ c3 := by rw [h13]
        _ = c4 := hL3
    have h35 : c3 = c5 := by
      calc
        c3 = x ◇ c2 := hL2.symm
        _ = x ◇ c4 := by rw [h24eq]
        _ = c5 := hL4
    have h2x : c2 = x := by
      calc
        c2 = c4 := h24eq
        _ = x ◇ c3 := hL3.symm
        _ = x ◇ c5 := by rw [h35]
        _ = x := hL5
    exact h02 h2x.symm
  have h15 : c1 ≠ c5 := by
    intro h15
    have h2x : c2 = x := by
      calc
        c2 = x ◇ c1 := hL1.symm
        _ = x ◇ c5 := by rw [h15]
        _ = x := hL5
    exact h02 h2x.symm
  have h1A : c1 ≠ A := by
    have hc1_orbit_eq : (fun z => x ◇ z)^[1] x = c1 := by
      simp [hL0]
    intro h1A
    exact hA_notin 1 (h1A.symm.trans hc1_orbit_eq.symm)
  have h23 : c2 ≠ c3 := by
    intro h23
    have h34 : c3 = c4 := by
      calc
        c3 = x ◇ c2 := hL2.symm
        _ = x ◇ c3 := by rw [h23]
        _ = c4 := hL3
    have h45 : c4 = c5 := by
      calc
        c4 = x ◇ c3 := hL3.symm
        _ = x ◇ c4 := by rw [h34]
        _ = c5 := hL4
    exact h25 (h23.trans (h34.trans h45))
  have h24 : c2 ≠ c4 := by
    intro h24
    have h35 : c3 = c5 := by
      calc
        c3 = x ◇ c2 := hL2.symm
        _ = x ◇ c4 := by rw [h24]
        _ = c5 := hL4
    have h2x : c2 = x := by
      calc
        c2 = c4 := h24
        _ = x ◇ c3 := hL3.symm
        _ = x ◇ c5 := by rw [h35]
        _ = x := hL5
    exact h02 h2x.symm
  have h2A_ne : c2 ≠ A := by
    have hc2_orbit_eq : (fun z => x ◇ z)^[2] x = c2 := by
      simp [Function.iterate_succ_apply', hL0, hL1]
    intro h2A
    exact hA_notin 2 (h2A.symm.trans hc2_orbit_eq.symm)
  have hA1 : A ◇ c1 = c1 := by
    rcases hcover (A ◇ c1) with hA1 | hA1 | hA1 | hA1 | hA1 | hA1 | hA1
    · have h12eq : c1 = c2 := d6_e677_left_cancel h A (hA1.trans hA2.symm)
      exact (h12 h12eq).elim
    · exact hA1
    · have h14eq : c1 = c4 := d6_e677_left_cancel h A (hA1.trans hA4.symm)
      have h25eq : c2 = c5 := by
        calc
          c2 = x ◇ c1 := hL1.symm
          _ = x ◇ c4 := by rw [h14eq]
          _ = c5 := hL4
      exact (h25 h25eq).elim
    · have h1x : c1 = x := d6_e677_left_cancel h A (hA1.trans hA0.symm)
      exact (h01 h1x.symm).elim
    · have h15eq : c1 = c5 := d6_e677_left_cancel h A (hA1.trans hA5.symm)
      exact (h15 h15eq).elim
    · have h1Aeq : c1 = A := d6_e677_left_cancel h A (hA1.trans hAA.symm)
      exact (h1A h1Aeq).elim
    · have h13eq : c1 = c3 := d6_e677_left_cancel h A (hA1.trans hA3.symm)
      exact (h13 h13eq).elim
  have hc2_image : c2 = A ◇ (c2 ◇ A) := by
    calc
      c2 = A ◇ (c2 ◇ ((A ◇ c2) ◇ A)) := h c2 A
      _ = A ◇ (c2 ◇ (x ◇ A)) := by rw [hA2]
      _ = A ◇ (c2 ◇ A) := by rw [hLA]
  have h2A4 : c2 ◇ A = c4 := by
    rcases hcover (c2 ◇ A) with h2A | h2A | h2A | h2A | h2A | h2A | h2A
    · have h23eq : c2 = c3 := by simpa [h2A, hA0] using hc2_image
      exact (h23 h23eq).elim
    · have h21 : c2 = c1 := by simpa [h2A, hA1] using hc2_image
      exact (h12 h21.symm).elim
    · have h2x : c2 = x := by simpa [h2A, hA2] using hc2_image
      exact (h02 h2x.symm).elim
    · have h2Aeq : c2 = A := by simpa [h2A, hA3] using hc2_image
      exact (h2A_ne h2Aeq).elim
    · exact h2A
    · have h24eq : c2 = c4 := by simpa [h2A, hA5] using hc2_image
      exact (h24 h24eq).elim
    · have h25eq : c2 = c5 := by simpa [h2A, hAA] using hc2_image
      exact (h25 h25eq).elim
  have h1c5 : c1 ◇ c5 = c1 := by
    apply d6_e677_left_cancel h A
    calc
      A ◇ (c1 ◇ c5) = c1 := by
        simpa [hA1, h1A5] using (h c1 A).symm
      _ = A ◇ c1 := hA1.symm
  have h1c2 : c1 ◇ c2 = A := by
    have htmp : A = c1 ◇ c2 := by
      calc
        A = c1 ◇ (A ◇ ((c1 ◇ A) ◇ c1)) := h A c1
        _ = c1 ◇ (A ◇ (c5 ◇ c1)) := by rw [h1A5]
        _ = c1 ◇ (A ◇ c4) := by rw [h5c1]
        _ = c1 ◇ c2 := by rw [hA4]
    exact htmp.symm
  have hc1_image : c1 ◇ (c2 ◇ c1) = c2 := by
    have htmp : c2 = c1 ◇ (c2 ◇ c1) := by
      calc
        c2 = c1 ◇ (c2 ◇ ((c1 ◇ c2) ◇ c1)) := h c2 c1
        _ = c1 ◇ (c2 ◇ (A ◇ c1)) := by rw [h1c2]
        _ = c1 ◇ (c2 ◇ c1) := by rw [hA1]
    exact htmp.symm
  rcases hcover (c2 ◇ c1) with h21 | h21 | h21 | h21 | h21 | h21 | h21
  · have h14eq : c4 = c2 := by simpa [h21, h1x4] using hc1_image
    exact h24 h14eq.symm
  · have h2c5 : c2 ◇ c5 = c1 := by
      have htmp : c1 = c2 ◇ c5 := by
        calc
          c1 = c2 ◇ (c1 ◇ ((c2 ◇ c1) ◇ c2)) := h c1 c2
          _ = c2 ◇ (c1 ◇ (c1 ◇ c2)) := by rw [h21]
          _ = c2 ◇ (c1 ◇ A) := by rw [h1c2]
          _ = c2 ◇ c5 := by rw [h1A5]
      exact htmp.symm
    have h2x5 : c2 ◇ x = c5 := by
      have htmp : c5 = c2 ◇ x := by
        calc
          c5 = c2 ◇ (c5 ◇ ((c2 ◇ c5) ◇ c2)) := h c5 c2
          _ = c2 ◇ (c5 ◇ (c1 ◇ c2)) := by rw [h2c5]
          _ = c2 ◇ (c5 ◇ A) := by rw [h1c2]
          _ = c2 ◇ x := by rw [h5A0]
      exact htmp.symm
    have hx1 : x = c1 := by
      have htmp : c1 = x ◇ c1 := by
        calc
          c1 = x ◇ (c1 ◇ ((x ◇ c1) ◇ x)) := h c1 x
          _ = x ◇ (c1 ◇ (c2 ◇ x)) := by rw [hL1]
          _ = x ◇ (c1 ◇ c5) := by rw [h2x5]
          _ = x ◇ c1 := by rw [h1c5]
      exact d6_e677_left_cancel h x (hL0.trans htmp)
    exact h01 hx1
  · have h2Aeq : c2 = A := by
      have htmp : A = c2 := by
        simpa [h21, h1c2] using hc1_image
      exact htmp.symm
    exact h2A_ne h2Aeq
  · rcases hcover (c2 ◇ x) with h2x | h2x | h2x | h2x | h2x | h2x | h2x
    · have h4x : c4 = x := by
        have htmp : c1 = x ◇ c4 := by
          calc
            c1 = x ◇ (c1 ◇ ((x ◇ c1) ◇ x)) := h c1 x
            _ = x ◇ (c1 ◇ (c2 ◇ x)) := by rw [hL1]
            _ = x ◇ (c1 ◇ x) := by rw [h2x]
            _ = x ◇ c4 := by rw [h1x4]
        exact d6_e677_left_cancel h x (htmp.symm.trans hL0.symm)
      exact h04 h4x.symm
    · have h4x : c4 = x := by
        have htmp : x = c2 ◇ A := by
          calc
            x = c2 ◇ (x ◇ ((c2 ◇ x) ◇ c2)) := h x c2
            _ = c2 ◇ (x ◇ (c1 ◇ c2)) := by rw [h2x]
            _ = c2 ◇ (x ◇ A) := by rw [h1c2]
            _ = c2 ◇ A := by rw [hLA]
        exact h2A4.symm.trans htmp.symm
      exact h04 h4x.symm
    · have h1Aeq : c1 = A := by
        calc
          c1 = x ◇ (c1 ◇ ((x ◇ c1) ◇ x)) := h c1 x
          _ = x ◇ (c1 ◇ (c2 ◇ x)) := by rw [hL1]
          _ = x ◇ (c1 ◇ c2) := by rw [h2x]
          _ = x ◇ A := by rw [h1c2]
          _ = A := hLA
      exact h1A h1Aeq
    · have hx1 : x = c1 := d6_e677_left_cancel h c2 (h2x.trans h21.symm)
      exact h01 hx1
    · have hxA : x = A := d6_e677_left_cancel h c2 (h2x.trans h2A4.symm)
      exact hA_notin 0 hxA.symm
    · have h12eq : c1 = c2 := by
        calc
          c1 = x ◇ (c1 ◇ ((x ◇ c1) ◇ x)) := h c1 x
          _ = x ◇ (c1 ◇ (c2 ◇ x)) := by rw [hL1]
          _ = x ◇ (c1 ◇ c5) := by rw [h2x]
          _ = x ◇ c1 := by rw [h1c5]
          _ = c2 := hL1
      exact h12 h12eq
    · have hx1 : x = c1 := by
        have htmp : c1 = x := by
          calc
            c1 = x ◇ (c1 ◇ ((x ◇ c1) ◇ x)) := h c1 x
            _ = x ◇ (c1 ◇ (c2 ◇ x)) := by rw [hL1]
            _ = x ◇ (c1 ◇ A) := by rw [h2x]
            _ = x ◇ c5 := by rw [h1A5]
            _ = x := hL5
        exact htmp.symm
      exact h01 hx1
  · have h1Aeq : c1 = A := d6_e677_left_cancel h c2 (h21.trans h2A4.symm)
    exact h1A h1Aeq
  · have h12eq : c1 = c2 := by simpa [h21, h1c5] using hc1_image
    exact h12 h12eq
  · have h25eq : c5 = c2 := by simpa [h21, h1A5] using hc1_image
    exact h25 h25eq.symm

theorem c5_branch_AA_eq_c5_and_Ax_eq_c3_false
    (C : D6Gap1Context α)
    (h1A5 : C.c1 ◇ C.A = C.c5)
    (hAA : C.A ◇ C.A = C.c5)
    (hA0 : C.A ◇ C.x = C.c3) :
    False := by
  have hA4 : C.A ◇ C.c4 = C.c2 :=
    c5_branch_AA_eq_c5_and_Ax_eq_c3_forces_Ac4_eq_c2 C h1A5 hAA hA0
  exact c5_branch_AA_eq_c5_and_Ax_eq_c3_and_Ac4_eq_c2_false C h1A5 hAA hA0 hA4

theorem fixer_of_c4_mul_x_eq_x
    (C : D6Gap1Context α)
    (hc4x : C.c4 ◇ C.x = C.x) :
    ((C.x ◇ C.x) ◇ C.x) ◇ C.x = C.x := by
  rcases C with
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  change c4 ◇ x = x at hc4x
  let C' : D6Gap1Context α :=
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  have hc1x : c1 ◇ x = c4 := c1_mul_x_eq_c4 C'
  calc
    ((x ◇ x) ◇ x) ◇ x = (c1 ◇ x) ◇ x := by rw [hL0]
    _ = c4 ◇ x := by rw [hc1x]
    _ = x := hc4x

theorem exact_packet_c3_mul_c1_eq_x
    (C : D6Gap1Context α)
    (hAA : C.A ◇ C.A = C.c1)
    (hA0 : C.A ◇ C.x = C.c3) :
    C.c3 ◇ C.c1 = C.x := by
  rcases C with
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  change A ◇ A = c1 at hAA
  change A ◇ x = c3 at hA0
  have hA3 : A ◇ c3 = A := by
    rw [← hA0]
    exact hA_Ax
  have htmp : A ◇ (c3 ◇ c1) = c3 := by
    simpa [hA3, hAA] using (h c3 A).symm
  exact d6_e677_left_cancel h A (htmp.trans hA0.symm)

theorem exact_packet_c1_mul_c4_eq_c3
    (C : D6Gap1Context α)
    (hAA : C.A ◇ C.A = C.c1)
    (hA0 : C.A ◇ C.x = C.c3)
    (hT1 : C.c3 ◇ C.c3 = C.c1) :
    C.c1 ◇ C.c4 = C.c3 := by
  rcases C with
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  change A ◇ A = c1 at hAA
  change A ◇ x = c3 at hA0
  change c3 ◇ c3 = c1 at hT1
  let C' : D6Gap1Context α :=
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  have hc3c1 : c3 ◇ c1 = x :=
    exact_packet_c3_mul_c1_eq_x C' hAA hA0
  have hEq : c1 = c3 ◇ (c1 ◇ c4) := by
    calc
      c1 = c3 ◇ (c1 ◇ ((c3 ◇ c1) ◇ c3)) := by simpa using (h c1 c3)
      _ = c3 ◇ (c1 ◇ (x ◇ c3)) := by rw [hc3c1]
      _ = c3 ◇ (c1 ◇ c4) := by rw [hL3]
  apply d6_e677_left_cancel h c3
  calc
    c3 ◇ (c1 ◇ c4) = c1 := hEq.symm
    _ = c3 ◇ c3 := hT1.symm

theorem exact_packet_c4_mul_x_eq_x
    (C : D6Gap1Context α)
    (hAA : C.A ◇ C.A = C.c1)
    (hA0 : C.A ◇ C.x = C.c3)
    (hT1 : C.c3 ◇ C.c3 = C.c1) :
    C.c4 ◇ C.x = C.x := by
  rcases C with
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  change A ◇ A = c1 at hAA
  change A ◇ x = c3 at hA0
  change c3 ◇ c3 = c1 at hT1
  let C' : D6Gap1Context α :=
    ⟨h, x, c1, c2, c3, c4, c5, A, hA_notin, hOrbitA, hcover,
      hL0, hL1, hL2, hL3, hL4, hL5, h02, h25, hLA, hA_Ax, hPhi, hAxAA⟩
  have hc3c1 : c3 ◇ c1 = x :=
    exact_packet_c3_mul_c1_eq_x C' hAA hA0
  have hc1c4 : c1 ◇ c4 = c3 :=
    exact_packet_c1_mul_c4_eq_c3 C' hAA hA0 hT1
  have hc1x : c1 ◇ x = c4 := c1_mul_x_eq_c4 C'
  have hEq : c4 = c1 ◇ (c4 ◇ x) := by
    calc
      c4 = c1 ◇ (c4 ◇ ((c1 ◇ c4) ◇ c1)) := by simpa using (h c4 c1)
      _ = c1 ◇ (c4 ◇ (c3 ◇ c1)) := by rw [hc1c4]
      _ = c1 ◇ (c4 ◇ x) := by rw [hc3c1]
  apply d6_e677_left_cancel h c1
  calc
    c1 ◇ (c4 ◇ x) = c4 := hEq.symm
    _ = c1 ◇ x := hc1x.symm

theorem fixer_of_exact_packet
    (C : D6Gap1Context α)
    (hAA : C.A ◇ C.A = C.c1)
    (hA0 : C.A ◇ C.x = C.c3)
    (hT1 : C.c3 ◇ C.c3 = C.c1) :
    ((C.x ◇ C.x) ◇ C.x) ◇ C.x = C.x :=
  fixer_of_c4_mul_x_eq_x C (exact_packet_c4_mul_x_eq_x C hAA hA0 hT1)

end D6Gap1Context
