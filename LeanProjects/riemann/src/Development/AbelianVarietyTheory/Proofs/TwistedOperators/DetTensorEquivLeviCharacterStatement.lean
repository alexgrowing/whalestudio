import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTensorEquivLeviCharacter
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_tensor_equiv_levi_character : ∀ (R β : Type) [CommRing R] [Fintype β] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (χ : β → Rˣ →* ℂˣ), Nonempty ((piTensor fun j => detRep (c j) (χ j)).Equiv (ofChar (leviChar c χ))) := by
  first | exact @GlobalTheory.SmGL.Exponents.nonempty_piTensor_detRep_equiv | exact GlobalTheory.SmGL.Exponents.nonempty_piTensor_detRep_equiv | (intros; apply GlobalTheory.SmGL.Exponents.nonempty_piTensor_detRep_equiv <;> assumption)
