import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionDifferential

namespace GroundTheory.Global

noncomputable section

open IsLocalRing NumberField IsDedekindDomain GroundTheory.Arith.Abelian

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev reductionLocalRing : Type _ := Localization.AtPrime v.asIdeal

instance reductionLocalRing.isDiscreteValuationRing :
    IsDiscreteValuationRing (reductionLocalRing v) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) v.ne_bot _

theorem reductionLocalRing.primeCompl_le : v.asIdeal.primeCompl ≤ nonZeroDivisors (𝓞 K) := by
  intro a ha
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact fun h => ha (h.symm ▸ v.asIdeal.zero_mem)

instance reductionLocalRing.algebra : Algebra (reductionLocalRing v) K :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _ v.asIdeal.primeCompl (nonZeroDivisors (𝓞 K))
    (reductionLocalRing.primeCompl_le v)

instance reductionLocalRing.isScalarTower : IsScalarTower (𝓞 K) (reductionLocalRing v) K :=
  IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _
    (reductionLocalRing.primeCompl_le v)

instance reductionLocalRing.isFractionRing : IsFractionRing (reductionLocalRing v) K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization v.asIdeal.primeCompl _ K

variable (W W' : WeierstrassCurve (reductionLocalRing v)) [W.IsElliptic] [W'.IsElliptic]

end

end GroundTheory.Global
