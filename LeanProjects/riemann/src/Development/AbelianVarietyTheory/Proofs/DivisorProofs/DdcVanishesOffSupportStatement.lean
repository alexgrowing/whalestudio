import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcVanishesOffSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_vanishes_off_support : ∀ (M : Type) [TopologicalSpace M] (A : HolAtlas M 1) (φ : ℂ → ℝ), HasCompactSupport φ → ∀ x : (famAtlas A).Pt, x.pt.2 ∉ ((↑) : ℂ → OnePoint ℂ) '' tsupport φ → (famAtlas A).ddc ((famAtlas A).fn fun y => y.2.elim 0 φ) x = 0 := by
  first | exact @GlobalTheory.BcUnique.ddc_elim_eq_zero_off_support | exact GlobalTheory.BcUnique.ddc_elim_eq_zero_off_support | (intros; apply GlobalTheory.BcUnique.ddc_elim_eq_zero_off_support <;> assumption)
