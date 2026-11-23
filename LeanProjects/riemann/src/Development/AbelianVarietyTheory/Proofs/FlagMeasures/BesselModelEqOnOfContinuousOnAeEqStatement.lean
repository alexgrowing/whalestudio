import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelEqOnOfContinuousOnAeEq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq : ∀ (k r : ℕ) {B : Type} [NormedAddCommGroup B] (μG : Measure (Mt k r)) (f g : Mat k r → B), IsHaarOn (GG k r) μG → ContinuousOn f (GG k r) → ContinuousOn g (GG k r) → (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] (fun x => g (Matrix.of x)) → ∀ x ∈ GG k r, f x = g x := by
  first | exact @GlobalTheory.SgInf.AeqCont.eqOn_of_ae | exact GlobalTheory.SgInf.AeqCont.eqOn_of_ae | (intros; apply GlobalTheory.SgInf.AeqCont.eqOn_of_ae <;> assumption)
