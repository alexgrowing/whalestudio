import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceFreeDerivCongrOnUnitaryGroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceFreeDeriv_congr_on_unitaryGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ) (a b : Fin n), (∀ g ∈ SUset ε, G₁ g = G₂ g) → ∀ g ∈ SUset ε, Ec ε (E0 a b) G₁ g = Ec ε (E0 a b) G₂ g := by
  first | exact @GlobalTheory.DSSU.Local.matrix_unit_action_congr | exact GlobalTheory.DSSU.Local.matrix_unit_action_congr | (intros; apply GlobalTheory.DSSU.Local.matrix_unit_action_congr <;> assumption)
