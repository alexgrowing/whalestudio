import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfCharpolySeparableInvolution
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable | exact GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable | (intros; apply GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable <;> assumption)
