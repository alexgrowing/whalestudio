import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraPermute
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_permute : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (s : Equiv.Perm (Fin n)), (∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) → StrictAnti (lam ∘ s) → IsHCU ε lam σ → IsHCDS (ε ∘ s) (lam ∘ s) (fun g => σ (g.submatrix s.symm s.symm)) := by
  first | exact @GlobalTheory.DSSU.Chamber.vChamber | exact GlobalTheory.DSSU.Chamber.vChamber | (intros; apply GlobalTheory.DSSU.Chamber.vChamber <;> assumption)
