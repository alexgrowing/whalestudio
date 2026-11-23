import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlurisubharmonicLocal
import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plurisubharmonic_local : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (φ : (Fin n → ℂ) → ℝ), IsOpen U → (∀ z ∈ U, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ z ∈ V ∧ ReciprocityTheory.AnForm.A.IsPsh V φ) → ReciprocityTheory.AnForm.A.IsPsh U φ := by
  first | exact @GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally | exact GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally | (intros; apply GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally <;> assumption)
