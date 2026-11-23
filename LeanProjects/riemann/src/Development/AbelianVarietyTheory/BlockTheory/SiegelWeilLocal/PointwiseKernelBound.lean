import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open NumberField Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PointwiseKernelBound

open Formalism.MainNotions.S GlobalTheory.Count

def decHS (q : ℕ) (h t : ℝ) : ℝ := Real.exp (-(h / 8) * min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))))

def PointwiseBound : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (h : ℝ),
    IsDSData B d → SigIs B p q → GapGe B h → 8 * (B.I.n : ℝ) * ((min p q : ℕ) : ℝ) < h →
      (1 ≤ min p q → ∀ y : B.I.GA,
          ‖phe B d y‖ ≤ (∏ v, d v) * (B.e 1).re * ∏ v, decHS (min p q) h (dHS (uMat (y.1 v)))) ∧
      (∀ y : B.I.GA, ‖phe B d y‖ ≤ (∏ v, d v) * (B.e 1).re) ∧
      phe B d 1 = ((∏ v, d v : ℝ) : ℂ) * B.e 1 ∧
      (B.e 1).im = 0 ∧ 0 ≤ (B.e 1).re ∧
      (∀ x : B.I.Gf, ‖B.e x‖ ≤ (B.e 1).re) ∧
      ∀ y : B.I.GA, phe B d y ≠ 0 → y.2 ∈ B.I.Kset

example (q : ℕ) (h : ℝ) : decHS q h 0 = 1 := by simp [decHS]

example (q : ℕ) (h t : ℝ) (hh : 0 ≤ h) (ht : 0 ≤ t) : decHS q h t ≤ 1 := by
  unfold decHS
  rw [Real.exp_le_one_iff]
  have : 0 ≤ min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) := le_min (by positivity) (by positivity)
  nlinarith [mul_nonneg hh this]

end GlobalTheory.IndefiniteRowSideFullHecke.PointwiseKernelBound
