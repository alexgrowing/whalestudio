import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralMatrixRelatingIntegralVectorZBases
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralMatrix_relating_integralVectorZBases : ∀ (I : AutInst) {N : ℕ} (e e₀ : Fin N → Fin I.n → I.E), IsZBasis I e → IsZBasis I e₀ →
    (∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis I.E k : I.E) • e j = ∑ i, z i • e i → (integralBasis I.E k : I.E) • e₀ j = ∑ i, z i • e₀ i) →
    ∃ M : Matrix (Fin I.n) (Fin I.n) I.E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j := by
  first | exact @GlobalTheory.CuspGeo.exists_integral_matrix_of_same_mul | exact GlobalTheory.CuspGeo.exists_integral_matrix_of_same_mul | (intros; apply GlobalTheory.CuspGeo.exists_integral_matrix_of_same_mul <;> assumption)
