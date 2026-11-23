import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsNefGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

universe u w

theorem curveClosure {S : Type u} [CommRing S] [IsDomain S] {F : Type u} [Field F] [Algebra S F]
    [IsFractionRing S F] {N : ℕ} (pp : Ideal (Poly F N)) [pp.IsPrime] :
    (∀ s : S, (C s : Poly S N) ∈ pp.comap (MvPolynomial.map (algebraMap S F)) → s = 0) ∧
      (pp.comap (MvPolynomial.map (algebraMap S F))).map (MvPolynomial.map (algebraMap S F)) = pp := by
  refine ⟨fun s hs => ?_, ?_⟩
  · by_contra h0
    have hs' : (C (algebraMap S F s) : Poly F N) ∈ pp := by
      rw [Ideal.mem_comap, map_C] at hs; exact hs
    have hu : IsUnit (C (algebraMap S F s) : Poly F N) :=
      (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective S F)).mpr h0)).map C
    exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ hs' hu)
  · let _ : Algebra (Poly S N) (Poly F N) := MvPolynomial.algebraMvPolynomial
    have : IsLocalization ((nonZeroDivisors S).map (C : S →+* Poly S N)) (Poly F N) :=
      MvPolynomial.isLocalization (nonZeroDivisors S) F
    exact IsLocalization.map_under ((nonZeroDivisors S).map (C : S →+* Poly S N)) (Poly F N) pp

theorem NefGeneric.proof (hC : ConservationOfDegree.Statement.{u, w}) :
    NefGeneric.Statement.{u, w} := by
  intro S _ _ F _ _ _ Ω _ _ _ _ N x M 𝔪 h𝔪 hM pp _ hpp
  have : pp.IsPrime := hpp.isPrime
  obtain ⟨hconst, hmap⟩ := curveClosure (S := S) pp
  have hpp' := hpp
  rw [← hmap] at hpp'
  have key := hC S F Ω N x M 𝔪 h𝔪 _ inferInstance hconst hpp'
  rw [hmap] at key
  rw [key]
  refine finsum_nonneg fun G => ?_
  split_ifs with hG
  · exact mul_nonneg (Int.natCast_nonneg _) (hM G (le_sup_right.trans hG.1.1.2) hG.2)
  · exact le_rfl

end GroundTheory.Heights₂.Heights.Kleiman
