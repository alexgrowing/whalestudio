import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast

noncomputable section
open NumberField GlobalTheory.DegCnt
namespace GlobalTheory.DegAsm

def pairBd (K : Type) [Field K] [NumberField K] (k g j T x x' : ℕ) : ℝ :=
  let f : ℕ := Formalism.HermitianLatticesTheory.fDeg K
  let Mb : ℝ := (20 * (f : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * (f : ℝ) * (6 + cf K))
  let D₀ : ℝ := (T : ℝ) ^ (2 * f)
  let Y : ℝ := (x : ℝ) * x' * D₀ ^ 2
  ((x : ℝ) * x') ^ ((k : ℝ) / 2) * Y ^ (6 * (j : ℝ) + 10 + 4 * cf K) *
    (1 + Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ f *
        (∑ s ∈ Finset.Ico 1 k, ((32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * Y ^ 7) ^ s) +
      ((2 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * D₀ * x * x') ^ k)

open NumberField in
private lemma vInv_nonneg' (K : Type) [Field K] [NumberField K] :
    0 ≤ _root_.Formalism.HermitianLatticesTheory.vInv K := by
  unfold _root_.Formalism.HermitianLatticesTheory.vInv
  positivity

open NumberField in

theorem _root_.GlobalTheory.DegAsm.pairBd_nonneg (K : Type) [Field K] [NumberField K]
    (k g j T x x' : ℕ) : 0 ≤ _root_.GlobalTheory.DegAsm.pairBd K k g j T x x' := by
  have hv := vInv_nonneg' K
  unfold _root_.GlobalTheory.DegAsm.pairBd
  dsimp only
  have hMb : 0 ≤ (20 * ((_root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) * (2 * _root_.Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^
      (2 * ((_root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) * (6 + _root_.GlobalTheory.DegCnt.cf K)) :=
    Real.rpow_nonneg (by positivity) _
  have hY : 0 ≤ (x : ℝ) * x' * ((T : ℝ) ^ (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K)) ^ 2 := by positivity
  have hxx : 0 ≤ (x : ℝ) * x' := by positivity
  refine mul_nonneg (mul_nonneg (Real.rpow_nonneg hxx _) (Real.rpow_nonneg hY _)) ?_
  refine add_nonneg (add_nonneg zero_le_one (mul_nonneg (mul_nonneg hMb (by positivity)) ?_))
    (by positivity)
  exact Finset.sum_nonneg fun s _ => by positivity

end GlobalTheory.DegAsm
