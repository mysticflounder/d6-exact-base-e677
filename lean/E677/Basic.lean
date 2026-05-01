import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# E677 → E255: Shared definitions

The last open implication in the finite magma equational theory lattice.
-/

universe u

class Magma' (α : Type u) where
  op : α → α → α

infixl:65 " ◇ " => Magma'.op

-- E677: x = y ◇ (x ◇ ((y ◇ x) ◇ y))
def E677 (α : Type u) [Magma' α] : Prop :=
  ∀ x y : α, x = y ◇ (x ◇ ((y ◇ x) ◇ y))

-- E255: x = ((x ◇ x) ◇ x) ◇ x
def E255 (α : Type u) [Magma' α] : Prop :=
  ∀ x : α, x = ((x ◇ x) ◇ x) ◇ x

-- E614: x = x ◇ (x ◇ ((x ◇ x) ◇ x))
def E614 (α : Type u) [Magma' α] : Prop :=
  ∀ x : α, x = x ◇ (x ◇ ((x ◇ x) ◇ x))

