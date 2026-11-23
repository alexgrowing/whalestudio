import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPotentialContinuousOn
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_potential_continuous_on : ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y] (A : ReciprocityTheory.AnForm.M.FinHolAtlas D Y) (Θ : ReciprocityTheory.AnForm.M.LocPot Y) (u : Y → ℝ) (S : Set Y) (x : Y) (Φ : OpenPartialHomeomorph Y (Fin D → ℂ)), IsOpen S → ReciprocityTheory.AnForm.M.IsPotential A Θ → A.SmoothOn S u → GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.SumNonnegOn A Θ u S → ReciprocityTheory.AnForm.M.IsCompatChart A Φ → IsOpen (Φ.target ∩ Φ.symm ⁻¹' (Θ.U x ∩ S)) ∧ ContinuousOn (fun w => 2 * Θ.φ x (Φ.symm w) + u (Φ.symm w)) (Φ.target ∩ Φ.symm ⁻¹' (Θ.U x ∩ S)) ∧ ReciprocityTheory.AnForm.A.IsPsh (Φ.target ∩ Φ.symm ⁻¹' (Θ.U x ∩ S)) (fun w => 2 * Θ.φ x (Φ.symm w) + u (Φ.symm w)) ∧ ∀ κ : ℝ, ReciprocityTheory.AnForm.A.IsPsh (Φ.target ∩ Φ.symm ⁻¹' (Θ.U x ∩ S)) (fun w => max (2 * Θ.φ x (Φ.symm w) + u (Φ.symm w)) (-κ)) := by
  first | exact @GlobalTheory.ChartPsh.isPsh_chart_sum | exact GlobalTheory.ChartPsh.isPsh_chart_sum | (intros; apply GlobalTheory.ChartPsh.isPsh_chart_sum <;> assumption)
