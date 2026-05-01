import E677.Basic

/-!
# Minimal core for the d=6 publication slice

This module intentionally avoids importing `E677.Core`.  It contains only the
small general E677 infrastructure needed by `D6Isolated.lean`:

* left multiplication is surjective from the E677 identity;
* on finite types, left multiplication is injective;
* the resulting left-cancellation rule;
* the backward recurrence used once in the d=6 packet proof.

The declarations use `d6_` prefixes so this file can be imported in the same
environment as the full `E677.Core` without name collisions.
-/

universe u

variable {α : Type u} [Magma' α]

set_option linter.unusedFintypeInType false

/-- E677 implies every left multiplication map is surjective. -/
theorem d6_e677_leftMul_surj (h : E677 α) (y : α) :
    Function.Surjective (fun x => y ◇ x) := by
  intro x
  exact ⟨x ◇ ((y ◇ x) ◇ y), (h x y).symm⟩

/-- E677 in the shifted form used by the backward recurrence. -/
theorem d6_e677_at_Lyx (h : E677 α) (x y : α) :
    y ◇ x = y ◇ ((y ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y)) :=
  h (y ◇ x) y

/-- On finite types, each E677 left multiplication map is bijective. -/
theorem d6_e677_leftMul_bij [Fintype α] (h : E677 α) (y : α) :
    Function.Bijective (fun x => y ◇ x) := by
  exact (Finite.surjective_iff_bijective).mp (d6_e677_leftMul_surj h y)

/-- On finite types, each E677 left multiplication map is injective. -/
theorem d6_e677_leftMul_inj [Fintype α] (h : E677 α) (y : α) :
    Function.Injective (fun x => y ◇ x) :=
  (d6_e677_leftMul_bij h y).1

/-- Left cancellation for finite E677 magmas. -/
theorem d6_e677_left_cancel [Fintype α] (h : E677 α) (y : α) {a b : α}
    (hab : y ◇ a = y ◇ b) : a = b :=
  d6_e677_leftMul_inj h y hab

/-- The backward recurrence used by the d=6 isolated packet proofs. -/
theorem d6_e677_backward_recurrence [Fintype α] (h : E677 α) (x y : α) :
    x = (y ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y) := by
  have h1 : y ◇ x = y ◇ ((y ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y)) :=
    d6_e677_at_Lyx h x y
  exact d6_e677_left_cancel h y h1
