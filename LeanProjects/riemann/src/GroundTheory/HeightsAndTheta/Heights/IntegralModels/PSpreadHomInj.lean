import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHom
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGenericSections
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsPullbackFaithful
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadBundle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

theorem SpreadHomInj.proof (h₁ : GenericSectionsInj.Statement)
    (h₂ : PullbackFaithful.Statement.{0}) : SpreadHomInj.Statement := by
  intro X f _ _ a ha F G hF hG
  obtain ⟨m, hm, H⟩ := h₁ X f
  refine ⟨m, hm, fun n hn hmn ψ₁ ψ₂ e => ?_⟩
  have hk : IsUnit (((a : ℤ) * n : ℤ) : ℚ) := isUnit_intCast_rat _ (by positivity)
  have hG' : IsVectorBundle
      ((Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a n))).obj G) :=
    hG.pullback_of_isOpenImmersion _
  refine h₂ _ _ (toInvOpen f ℚ ((a : ℤ) * n) hk)
    (H _ hk (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hmn) _)) _ _ hG' ψ₁ ψ₂ ?_
  unfold pullbackHomAlong at e
  rwa [cancel_epi, cancel_mono] at e

end GroundTheory.Heights₂.Heights.Model
