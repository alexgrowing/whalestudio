import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory

theorem cutWeight_contDiffOn_mem_Icc : ∀ {ι : Type} [Fintype ι] {χ : ℝ → ℝ}, IsCutoff χ → ∀ (κ : ℝ) {R : ℝ}, 2 ≤ R →
    ∀ {U : Set (ι → ℂ)} {r : (ι → ℂ) → ℝ}, ContDiffOn ℝ ∞ r U → (∀ z ∈ U, Real.exp 1 ≤ r z) →
    ContDiffOn ℝ ∞ (cutWeight χ κ R r) U ∧ ∀ z ∈ U, cutWeight χ κ R r z ∈ Icc (0 : ℝ) 1 := by
  intro ι _ χ hχ κ R hR U r hr hre
  have hRpos : 0 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  have hrpos : ∀ z ∈ U, 0 < r z := fun z hz => lt_of_lt_of_le (Real.exp_pos 1) (hre z hz)
  have hlogr : ∀ z ∈ U, 1 ≤ Real.log (r z) := by
    intro z hz
    rw [Real.le_log_iff_exp_le (hrpos z hz)]
    exact hre z hz
  have hq : ∀ z ∈ U, 0 ≤ Real.log (r z) / Real.log R := fun z hz =>
    div_nonneg (by linarith [hlogr z hz]) hlogR.le
  have hden : ∀ z ∈ U, 1 ≤ 1 + (r z / R) ^ κ := fun z hz => by
    have : 0 ≤ (r z / R) ^ κ := Real.rpow_nonneg (div_nonneg (hrpos z hz).le hRpos.le) κ
    linarith
  refine ⟨?_, ?_⟩
  · have hL : ContDiffOn ℝ ∞ (fun z => Real.log (r z) / Real.log R) U :=
      (hr.log fun z hz => (hrpos z hz).ne').div_const _
    have hC : ContDiffOn ℝ ∞ (fun z => χ (Real.log (r z) / Real.log R)) U :=
      hχ.smooth.comp hL (fun z hz => hq z hz)
    have hP : ContDiffOn ℝ ∞ (fun z => (r z / R) ^ κ) U :=
      (hr.div_const R).rpow_const_of_ne fun z hz => (div_pos (hrpos z hz) hRpos).ne'
    have hD : ContDiffOn ℝ ∞ (fun z => 1 + (r z / R) ^ κ) U := contDiffOn_const.add hP
    exact hC.div hD fun z hz => (lt_of_lt_of_le one_pos (hden z hz)).ne'
  · intro z hz
    have hm := hχ.mem _ (hq z hz)
    unfold cutWeight
    refine ⟨div_nonneg hm.1 (by linarith [hden z hz]), ?_⟩
    exact div_le_one_of_le₀ (le_trans hm.2 (hden z hz)) (by linarith [hden z hz])

end GlobalTheory
