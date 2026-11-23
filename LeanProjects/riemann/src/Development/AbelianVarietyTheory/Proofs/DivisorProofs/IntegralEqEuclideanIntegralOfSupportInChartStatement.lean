import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqEuclideanIntegralOfSupportInChart
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_euclidean_integral_of_support_in_chart : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld) (i : A.ι) (K : Set M), A.IsForm α → IsCompact K → K ⊆ (A.e i).source → (∀ x : A.Pt, x.pt ∉ K → α x = 0) → A.integral α = ∫ v, (GlobalTheory.CxForm.dens (A.loc α i v)).re := by
  first | exact @GlobalTheory.CxForm.HolAtlas.integral_eq_integral_chart_of_support | exact GlobalTheory.CxForm.HolAtlas.integral_eq_integral_chart_of_support | (intros; apply GlobalTheory.CxForm.HolAtlas.integral_eq_integral_chart_of_support <;> assumption)
