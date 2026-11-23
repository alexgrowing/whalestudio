import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StConormalGenerationGeneric
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GenericGradient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial KaehlerDifferential TensorProduct IsLocalRing

theorem ConormalGenerationGeneric.D_eq_sum_pderiv {n : ℕ} (g : MvPolynomial (Fin n) ℂ) :
    D ℂ (MvPolynomial (Fin n) ℂ) g = ∑ l, pderiv l g • D ℂ (MvPolynomial (Fin n) ℂ) (X l) := by
  conv_lhs => rw [← (mvPolynomialBasis ℂ (Fin n)).sum_repr (D ℂ _ g)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mvPolynomialBasis_repr_apply]
  congr 1
  rw [← (mvPolynomialBasis ℂ (Fin n)).repr_symm_single_one, mvPolynomialBasis_repr_symm_single, one_smul]

theorem ConormalGenerationGeneric.proof : ConormalGenerationGeneric.Statement :=
  _root_.UpperTheory.Reformulated.B.Qf34.proof

end

end GroundTheory.Heights₂.Heights
