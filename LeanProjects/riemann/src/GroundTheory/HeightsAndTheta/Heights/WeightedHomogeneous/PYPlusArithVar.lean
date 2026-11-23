import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

theorem YPlusArithVar.proof (hPrime : ChartPrimality.Statement) (hDim : ExtensionDimension.Statement) :
    YPlusArithVar.Statement := by
  intro ι _ _ n P D Ω _ y x' E hR hA
  obtain ⟨Q, hQ⟩ := hPrime ι n P D
  obtain ⟨_, _, _, hd⟩ := hA
  rw [← hR.ext_eq]
  refine ⟨inferInstance, hQ ▸ Q.isMultiProjPrime, hQ ▸ Q.isHorizontal, ?_⟩
  rw [← hR.ideal_eq] at hd
  change ringKrullDim (MvPolynomial (Coord D.extSizes) ℤ ⧸ D.extIdeal) = _
  rw [hDim ι n P D]
  change ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ P.ideal) + 1 = _
  change ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ P.ideal) = _ at hd
  rw [hd, Fintype.card_option]
  norm_cast

end GroundTheory.Heights₂.Heights
