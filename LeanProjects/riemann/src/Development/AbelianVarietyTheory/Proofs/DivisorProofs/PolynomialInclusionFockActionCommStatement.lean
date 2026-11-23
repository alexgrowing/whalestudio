import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialInclusionFockActionComm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IncMatTransposeConjTranspose
open scoped TensorProduct Matrix
open NumberField Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.FockIncl GlobalTheory.FockInclK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_inclusion_fock_action_comm : ∀ (P Q R S : ℕ) (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (Y : Mat R S),
    (polIncl P Q r₀ s₀).toLinearMap ∘ₗ fockAct2 P Q R S Y =
      fockAct2 P Q (R + 1) (S + 1) (extMat r₀ s₀ Y) ∘ₗ (polIncl P Q r₀ s₀).toLinearMap := by
  first | exact @GlobalTheory.FockInclAct.polIncl_comp_fockAct2 | exact GlobalTheory.FockInclAct.polIncl_comp_fockAct2 | (intros; apply GlobalTheory.FockInclAct.polIncl_comp_fockAct2 <;> assumption)
