import Mathlib

open Matrix

noncomputable section

namespace PositivityTheory.KB.HeightDistance

def nsq {N : ℕ} (v : Fin N → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

def dist1 {ι : Type} [Fintype ι] {N : ℕ} (A : ι → Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (1 + ∑ w, ∑ i, ∑ j, ‖A w i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖) ^ 2

theorem nsq_nonneg {N : ℕ} (v : Fin N → ℂ) : 0 ≤ nsq v :=
  Finset.sum_nonneg fun i _ => by positivity

theorem one_le_dist1 {ι : Type} [Fintype ι] {N : ℕ} (A : ι → Matrix (Fin N) (Fin N) ℂ) :
    1 ≤ dist1 A := by
  unfold dist1
  have h0 : 0 ≤ ∑ w, ∑ i, ∑ j, ‖A w i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ :=
    Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  nlinarith

end PositivityTheory.KB.HeightDistance
