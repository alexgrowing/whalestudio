import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySmoothBoundPotential
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_smooth_bound_potential : ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] (A : ReciprocityTheory.AnForm.M.FinHolAtlas D Y) (L : ReciprocityTheory.AnForm.M.LocPot Y) (s : Y → Y → ℂ) (m : ℕ) (W : Fin m → Set Y), GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.IsBoundary A L s W → ∀ (Θ : ReciprocityTheory.AnForm.M.LocPot Y) (u : Y → ℝ) (C₁ : ℝ), ReciprocityTheory.AnForm.M.IsPotential A Θ → A.SmoothOn (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s) u → GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.SumNonnegOn A Θ u (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s) → (∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s, u y ≤ C₁ * Real.log (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.rad L s y)) → ∀ (x : Y) (j : Fin A.n) (z₀ : Fin D → ℂ), z₀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.chartPart A j (Θ.U x) → (A.chart j).symm z₀ ∉ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s → ∃ V : Set (Fin D → ℂ), IsOpen V ∧ z₀ ∈ V ∧ (∃ M : ℝ, ∀ z ∈ V, (A.chart j).symm z ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s → u ((A.chart j).symm z) ≤ M) ∧ ∀ κ : ℝ, ReciprocityTheory.AnForm.A.IsPsh V (fun z => (max (((2 * Θ.φ x ((A.chart j).symm z) : ℝ) : EReal) + GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.limsupExt (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s) u ((A.chart j).symm z)) ((-κ : ℝ) : EReal)).toReal) := by
  first | exact @GlobalTheory.BdryChart.psh_near_boundary | exact GlobalTheory.BdryChart.psh_near_boundary | (intros; apply GlobalTheory.BdryChart.psh_near_boundary <;> assumption)
