import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPshOfLocallyIsPsh
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPsh_of_locally_isPsh : ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ), IsOpen U → (∀ z ∈ U, ∃ V : Set (Fin D → ℂ), IsOpen V ∧ z ∈ V ∧ ReciprocityTheory.AnForm.A.IsPsh V φ) → ReciprocityTheory.AnForm.A.IsPsh U φ := by
  first | exact @GlobalTheory.PshLocal.isPsh_of_local | exact GlobalTheory.PshLocal.isPsh_of_local | (intros; apply GlobalTheory.PshLocal.isPsh_of_local <;> assumption)
