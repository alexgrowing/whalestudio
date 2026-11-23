import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryLocalChartExists
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_local_chart_exists : ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] (A : ReciprocityTheory.AnForm.M.FinHolAtlas D Y) (L : ReciprocityTheory.AnForm.M.LocPot Y) (s : Y → Y → ℂ) (m : ℕ) (W : Fin m → Set Y), GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.IsBoundary A L s W → ∀ (y₀ : Y) (N : Set Y), IsOpen N → y₀ ∈ N → ∃ (Φ : OpenPartialHomeomorph Y (Fin D → ℂ)) (S : Finset (Fin D)) (K : Set Y) (a : ℝ), ReciprocityTheory.AnForm.M.IsCompatChart A Φ ∧ y₀ ∈ Φ.source ∧ Φ y₀ = 0 ∧ Φ.target = Metric.ball 0 1 ∧ IsCompact K ∧ Φ.source ⊆ K ∧ K ⊆ N ∧ (∀ y ∈ Φ.source, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s ↔ Φ y ∉ ReciprocityTheory.AnForm.A.coordDiv S) ∧ 0 ≤ a ∧ ∀ y ∈ Φ.source, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s → Real.log (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.rad L s y) ≤ a * Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖Φ y i‖⁻¹) := by
  first | exact @GlobalTheory.AdaptedChart.exists_adapted | exact GlobalTheory.AdaptedChart.exists_adapted | (intros; apply GlobalTheory.AdaptedChart.exists_adapted <;> assumption)
