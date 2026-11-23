import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimpleHeckePolyTransportRingEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimpleHeckePoly_transport_ringEquiv : ∀ (N l w : ℕ) {E : Type} [Field E] (ι : E ≃+* ℂ) (lam : Letter → E), SSPotB N l w (fun T => ι (lam T)) → ∃ P ∈ admissibleLettersSubalgebra E N l, FreeAlgebra.lift E lam P = 1 ∧ ∀ F ∈ Pot E w (Gam N l), ∀ T : Letter, admitted N l T → (opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E))) (FreeAlgebra.lift E (opL E N l) P F) ∈ Triv E w (Gam N l) := by
  first | exact @GlobalTheory.KZ.ssPot_transport | exact GlobalTheory.KZ.ssPot_transport | (intros; apply GlobalTheory.KZ.ssPot_transport <;> assumption)
