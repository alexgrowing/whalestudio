import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryToSpecialUnitaryLocal
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_to_special_unitary_local : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool), (∀ g ∈ UJset ε, ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ g₀ ∈ SUset ε, g = z • g₀ ∧ (g ∈ Kset ε ↔ g₀ ∈ KS ε)) ∧ (∀ z : ℂ, ‖z‖ = 1 → ∀ g₀ ∈ SUset ε, z • g₀ ∈ UJset ε ∧ (g₀ ∈ KS ε → z • g₀ ∈ Kset ε)) ∧ ∀ g ∈ UJset ε, ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (ζ : Matrix (Fin n) (Fin n) ℂ → ℂ), IsOpen U ∧ g ∈ U ∧ ContinuousOn ζ U ∧ ∀ x ∈ U, x ∈ UJset ε → ‖ζ x‖ = 1 ∧ (ζ x)⁻¹ • x ∈ SUset ε := by
  first | exact @GlobalTheory.SUSplit.unit_scalar_split | exact GlobalTheory.SUSplit.unit_scalar_split | (intros; apply GlobalTheory.SUSplit.unit_scalar_split <;> assumption)
