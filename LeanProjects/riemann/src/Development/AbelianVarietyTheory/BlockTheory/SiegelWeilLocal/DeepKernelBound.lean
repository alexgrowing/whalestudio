import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open MeasureTheory NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound

open Formalism.MainNotions.S GlobalTheory.Count

def dimN (B : RowsAut) : ℕ := B.I.n ^ 2 * B.I.f

def stepBe (n : ℕ) (b : ℝ) (P : ℕ) : ℝ :=
  Real.sqrt n * b ^ 2 + 3 / 2 * ((n : ℝ) * Real.sqrt n) + 3 * (P : ℝ)

def radRh (B : RowsAut) (q : ℕ) (τ : ℝ) : ℝ :=
  (B.I.n : ℝ) ^ 2 * Real.sqrt B.I.f * B.g * B.I.rd * (2 * τ) ^ ((1 : ℝ) / q) / 4

def DeepKernelBound : Prop :=
  ∀ (Cg : ℝ) (n₀ : ℕ) (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ)
    (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA),
    0 ≤ Cg → 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b →
    (∀ v, IsGauge (B.I.ε v) (c v)) →
    least B.I x < tauStar B q b →
    (kern B.I (phe B d) x x).re ≤
      (2 * radRh B q (least B.I x) * Real.sqrt B.I.f *
            stepBe B.I.n b (8 * q * dimN B + dimN B)) ^ (16 * q * dimN B) *
        (6 * stepBe B.I.n b (8 * q * dimN B + dimN B)) ^ dimN B *
        Real.exp B.I.f *
        (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * dimN B) *
        (B.D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal

example (n : ℕ) (b : ℝ) {P P' : ℕ} (h : P ≤ P') : stepBe n b P ≤ stepBe n b P' := by
  unfold stepBe
  have : (P : ℝ) ≤ P' := by exact_mod_cast h
  linarith

example : stepBe 4 1 2 = 20 := by
  have : Real.sqrt (4 : ℕ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  unfold stepBe
  rw [this]; norm_num

end GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound
