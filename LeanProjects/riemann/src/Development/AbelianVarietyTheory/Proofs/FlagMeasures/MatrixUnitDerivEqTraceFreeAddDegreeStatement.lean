import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixUnitDerivEqTraceFreeAddDegree
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixUnitDeriv_eq_traceFree_add_degree : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (m : ℤ) (G : Matrix (Fin n) (Fin n) ℂ → ℂ), SmoothOnG ε G → (∀ z : ℂ, ‖z‖ = 1 → ∀ x : Matrix (Fin n) (Fin n) ℂ, inUJ ε x → G (z • x) = z ^ m * G x) → ∀ (a b : Fin n) (x : Matrix (Fin n) (Fin n) ℂ), inUJ ε x → Eab ε a b G x = Ec ε (E0 a b) G x + (if a = b then (m : ℂ) / n else 0) * G x := by
  first | exact @GlobalTheory.CentralLetter.main | exact GlobalTheory.CentralLetter.main | (intros; apply GlobalTheory.CentralLetter.main <;> assumption)
