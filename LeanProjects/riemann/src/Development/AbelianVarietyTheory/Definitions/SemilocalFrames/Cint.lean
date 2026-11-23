import Mathlib

noncomputable section
open scoped Classical

namespace GlobalTheory.IdxInt

variable {W : Type} [AddCommGroup W]

def Fine (A : AddSubgroup W) (φ : W → ℂ) (B : AddSubgroup W) : Prop :=
  B ≤ A ∧ B.relIndex A ≠ 0 ∧ (∀ w, ∀ b ∈ B, φ (w + b) = φ w) ∧
    ((fun w => (QuotientAddGroup.mk w : W ⧸ B)) '' Function.support φ).Finite

def Nice (A : AddSubgroup W) (φ : W → ℂ) : Prop := ∃ B, Fine A φ B

def cint (A : AddSubgroup W) (φ : W → ℂ) : ℂ :=
  if h : Nice A φ then (∑ᶠ c : W ⧸ h.choose, φ c.out) / (h.choose.relIndex A : ℂ) else 0

def ind (P : W → Prop) : W → ℂ := fun w => if P w then 1 else 0

end GlobalTheory.IdxInt
