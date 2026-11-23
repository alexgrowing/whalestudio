import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFiniteAlgebraLengthSum
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PLengthDecomp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KrullDimQuotientEqOneIffEqBot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Module IsLocalRing

noncomputable section

universe u

namespace FiniteBirationalLength

theorem length_quot_maximal_eq_inertiaDeg {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (𝔫 : Ideal B) [𝔫.IsMaximal] :
    Module.length A (B ⧸ 𝔫) = (𝔫.inertiaDeg A : ℕ∞) := by
  have hmax : (𝔫.under A).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔫
  have hm : 𝔫.under A = maximalIdeal A := IsLocalRing.eq_maximalIdeal hmax
  have : 𝔫.LiesOver (maximalIdeal A) := ⟨hm.symm⟩
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  have : Module.Finite (A ⧸ maximalIdeal A) (B ⧸ 𝔫) :=
    Module.Finite.of_restrictScalars_finite A _ _
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) 𝔫,
    Module.length_eq_of_surjective (R := A ⧸ maximalIdeal A) (S := A) Ideal.Quotient.mk_surjective,
    Module.length_eq_finrank]

theorem full : FiniteBirationalLength.Statement.{u} := by
  intro A B _ _ _ _ _ _ _ _ hdim hinj hrank z hz
  classical
  have hfinMS := Vertical.LengthDecomp.finite_maximalSpectrum (R := A) (B := B)
  have hfin : Finite {𝔫 : Ideal B // 𝔫.IsMaximal} :=
    Finite.of_injective
      (fun 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal} => (⟨𝔫.1, 𝔫.2⟩ : MaximalSpectrum B))
      (fun a b h => Subtype.ext (congrArg MaximalSpectrum.asIdeal h))
  refine ⟨hfin, ?_⟩
  let : Fintype {𝔫 : Ideal B // 𝔫.IsMaximal} := Fintype.ofFinite _
  have : Module.IsTorsionFree A B := isTorsionFree_iff_algebraMap_injective.mpr hinj
  have h1 := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula A B z hdim hz
  rw [hrank, Nat.cast_one, one_mul, Ring.ord] at h1
  let hP : ∀ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal}, 𝔫.1.IsPrime := fun 𝔫 => 𝔫.2.isPrime
  have h2 := FieldNumbers.FiniteAlgebraLengthSum.proof A B {𝔫 : Ideal B // 𝔫.IsMaximal}
    (fun 𝔫 => 𝔫.1) (fun 𝔫 => 𝔫.2) Subtype.val_injective (fun M hM => ⟨⟨M, hM⟩, rfl⟩)
    (fun 𝔫 => Localization.AtPrime 𝔫.1) (fun 𝔫 => inferInstance) z
  rw [← h1, h2, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun 𝔫 _ => ?_
  have := 𝔫.2
  rw [length_quot_maximal_eq_inertiaDeg, Ring.ord]

end FiniteBirationalLength

end

end GroundTheory.Heights₂.Heights.NumbersDVR
