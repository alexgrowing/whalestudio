import Formalism.PeriodIntegrals.SzEatI

noncomputable section

namespace PI.SzEatI.W

open Formalism.BasicNotions Formalism.MainNotions.G

def rest {D : D7} (L : SizeData₂ D) (K : Consts) (ce : ErrC) (j p : ℕ) : ℝ :=
  EatI L K ce j p - max 0 ((∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ))

def Rt {D : D7} (L : SizeData₂ D) (K : Consts) : ℝ :=
  Nm D ^ 2 * (Real.log (8 * (D.R.n : ℝ) * Nm D * L.sc.a) + Real.log (L.sc.X'' D.R.n)) +
    |K.dl1| * Nm D ^ 2 * Real.log (2 * L.sc.a) + 2 * |K.dl2| * Real.log (2 * L.sc.a) ^ 2

def c1 (ce : ErrC) : ℝ := 12 + 5 * |ce.c6|

def StepW : Prop :=
  ∀ (D : D7) (L : SizeData₂ D), Formalism.MainNotions.SizesAt L → L.sc.b' ≤ L.sc.b →
    ∀ j ∈ SizeData₂.lifts D, ∀ z : Bool × HH D, 0 ≤ wPl D j z ∧ wPl D j z ≤ 3 * L.sc.b + L.etaSz + 1

def StepP : Prop :=
  ∀ (K : Consts) (ce : ErrC) (D : D7) (L : SizeData₂ D), Formalism.MainNotions.SizesAt L → L.sc.b' ≤ L.sc.b →
    ∀ j ∈ SizeData₂.lifts D, ∀ p : ℕ, p.Prime → (p : ℝ) ≤ L.sc.X'' D.R.n →
      Real.log p * rest L K ce j p ≤
        c1 ce * (D.R.f : ℝ) * L.sc.b * (Real.log p / p) + (D.R.f : ℝ) * Rt L K

def StepA : Prop :=
  ∀ (K : Consts) (eps : ℝ), ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D), L.sc.eps = eps → x0 ≤ L.sc.x →
    Formalism.MainNotions.SizesAt L →
      L.sc.b' ≤ L.sc.b ∧ 0 ≤ Rt L K ∧ L.sc.X'' D.R.n * Rt L K ≤ L.sc.b ∧ 1 < L.sc.X'' D.R.n ∧ 1 ≤ Real.log (L.sc.X'' D.R.n)

theorem card_le_of_le (S : Finset ℕ) (Y : ℝ) (hY : 0 ≤ Y) (h : ∀ p ∈ S, 1 ≤ p ∧ (p : ℝ) ≤ Y) :
    (S.card : ℝ) ≤ Y := by
  have hsub : S ⊆ Finset.Icc 1 ⌊Y⌋₊ := by
    intro p hp
    obtain ⟨h1, h2⟩ := h p hp
    exact Finset.mem_Icc.mpr ⟨h1, Nat.le_floor h2⟩
  have hc : S.card ≤ ⌊Y⌋₊ := by
    calc S.card ≤ (Finset.Icc 1 ⌊Y⌋₊).card := Finset.card_le_card hsub
      _ = ⌊Y⌋₊ := by simp
  calc (S.card : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast hc
    _ ≤ Y := Nat.floor_le hY

end PI.SzEatI.W
