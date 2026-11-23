import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWtExistsInvForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algWt_exists_invForm' : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n), ∃ β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ, GlobalTheory.CoefDuty.IsInvForm a β := by
  first | exact @GlobalTheory.algWt_exists_invForm | exact GlobalTheory.algWt_exists_invForm | (intros; apply GlobalTheory.algWt_exists_invForm <;> assumption)
