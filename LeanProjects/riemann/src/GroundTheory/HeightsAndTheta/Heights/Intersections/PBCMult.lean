import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBaseChange
import GroundTheory.HeightsAndTheta.Heights.Intersections.PReducedCutLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial IsLocalRing
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

noncomputable section

namespace BCMultProof

theorem length_quot_map_of_flat {A L : Type*} [CommRing A] [IsLocalRing A] [CommRing L]
    [IsLocalRing L] (φ : A →+* L) [IsLocalHom φ] (hflat : φ.Flat)
    (hmax : (maximalIdeal A).map φ = maximalIdeal L) (J : Ideal A) :
    Module.length L (L ⧸ J.map φ) = Module.length A (A ⧸ J) := by
  let _ := φ.toAlgebra
  have : Module.Flat A L := hflat
  have : IsLocalHom (algebraMap A L) := ‹IsLocalHom φ›
  have key := IsLocalRing.length_baseChange A L (A ⧸ J)
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot L J).toLinearEquiv.length_eq,
    RingHom.algebraMap_toAlgebra, hmax] at key
  have h1 : Module.length L (L ⧸ maximalIdeal L) = 1 :=
    Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩)
  rw [h1, mul_one] at key
  exact key

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [DecidableEq K] in

theorem flat_map : (MvPolynomial.map (algebraMap ℚ ℂ) : MRing ι ℚ →+* MRing ι ℂ).Flat :=
  ReciprocityTheory.AnForm.R.BaseChangeC.flat_mvPolynomial_rat_complex (σ := Σ k, ι k)

end BCMultProof

open BCMultProof BaseChange

theorem BCMult.intersectionNumber_baseChange : BCMult.Statement := by
  intro K _ _ ι _ P0 e s a W Wa hP hs hsP hW hWa
  classical
  have := hP.1.isPrime
  have : W.IsPrime := hW.1.1.1
  have : Wa.IsPrime := hWa.1.1
  have hWc : Wa.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = W :=
    ReciprocityTheory.AnForm.R.comap_of_mem_minimalPrimes_extC W Wa hWa
  have hrel : NumbersDVR.IsRelevant Wa := isRelevant_of_comap hW.2 hWc
  have hext : (P0 ⊔ Ideal.span {s}).map (MvPolynomial.map (algebraMap ℚ ℂ)) =
      extC P0 ⊔ Ideal.span {sC s} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    rfl

  have hWaMin : Wa ∈ (extC P0 ⊔ Ideal.span {sC s}).minimalPrimes := by
    rw [← hext]
    refine ⟨⟨‹Wa.IsPrime›, (Ideal.map_mono hW.1.1.2).trans hWa.1.2⟩, fun Q hQ hQWa => ?_⟩
    have : Q.IsPrime := hQ.1
    have hle : Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) ≤ W := hWc ▸ Ideal.comap_mono hQWa
    have hge : W ≤ Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) :=
      hW.1.2 ⟨Ideal.IsPrime.comap _, Ideal.map_le_iff_le_comap.mp hQ.2⟩ hle
    exact hWa.2 ⟨this, Ideal.map_le_iff_le_comap.mpr hge⟩ hQWa

  have hcomp : (Localization.localRingHom W Wa (MvPolynomial.map (algebraMap ℚ ℂ)) hWc.symm).comp
      (algebraMap (MRing ι ℚ) (Localization.AtPrime W)) =
      (algebraMap (MRing ι ℂ) (Localization.AtPrime Wa)).comp
        (MvPolynomial.map (algebraMap ℚ ℂ)) :=
    RingHom.ext fun z => Localization.localRingHom_to_map _ _ _ hWc.symm z
  have hmaxL : (maximalIdeal (Localization.AtPrime W)).map
      (Localization.localRingHom W Wa (MvPolynomial.map (algebraMap ℚ ℂ)) hWc.symm) =
      maximalIdeal (Localization.AtPrime Wa) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W), Ideal.map_map, hcomp,
      ← Ideal.map_map]
    exact map_eq_maximalIdeal_of_isRadical (ReciprocityTheory.AnForm.R.extC_isRadical W) hWa
  have hflat := length_quot_map_of_flat
    (Localization.localRingHom W Wa (MvPolynomial.map (algebraMap ℚ ℂ)) hWc.symm)
    (RingHom.Flat.localRingHom flat_map Wa W hWc.symm) hmaxL
    ((P0 ⊔ Ideal.span {s}).map (algebraMap (MRing ι ℚ) (Localization.AtPrime W)))
  have hJ : ((P0 ⊔ Ideal.span {s}).map (algebraMap (MRing ι ℚ) (Localization.AtPrime W))).map
      (Localization.localRingHom W Wa (MvPolynomial.map (algebraMap ℚ ℂ)) hWc.symm) =
      (extC P0 ⊔ Ideal.span {sC s}).map (algebraMap (MRing ι ℂ) (Localization.AtPrime Wa)) := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, hext]
  have h1 : NumbersDVR.multAt (P0 ⊔ Ideal.span {s}) W =
      NumbersDVR.multAt (extC P0 ⊔ Ideal.span {sC s}) Wa := by
    unfold NumbersDVR.multAt
    rw [ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient,
      ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient, ← hJ, hflat]

  have h2 : NumbersDVR.multAt (extC P0 ⊔ Ideal.span {sC s}) Wa =
      ∑ᶠ Z ∈ (extC P0).minimalPrimes, NumbersDVR.multAt (Z ⊔ Ideal.span {sC s}) Wa :=
    ReducedCutLength.intersectionNumber_baseChange (MRing ι ℂ) (extC P0) (sC s) Wa (ReciprocityTheory.AnForm.R.extC_isRadical P0)
      (fun _ hZ => sC_not_mem (comap_extC hZ) hsP) hWaMin
  have hfin : NumbersDVR.multAt (extC P0 ⊔ Ideal.span {sC s}) Wa ≠ ⊤ :=
    NumbersDVR.length_localizedQuot_ne_top _ Wa hWaMin

  have hterm : ∀ Z ∈ (extC P0).minimalPrimes, NumbersDVR.divCycle Z (sC s) Wa =
      ((NumbersDVR.multAt (Z ⊔ Ideal.span {sC s}) Wa).toNat : ℤ) := by
    intro Z hZ
    unfold NumbersDVR.divCycle
    by_cases hZW : Z ⊔ Ideal.span {sC s} ≤ Wa
    · have hm : Wa ∈ (Z ⊔ Ideal.span {sC s}).minimalPrimes :=
        ⟨⟨‹Wa.IsPrime›, hZW⟩, fun Q hQ hQW =>
          hWaMin.2 ⟨hQ.1, (sup_le_sup_right hZ.1.2 _).trans hQ.2⟩ hQW⟩
      rw [dif_pos ⟨hm, hrel⟩]
    · rw [dif_neg (fun h => hZW h.1.1.2)]
      unfold NumbersDVR.multAt
      rw [Module.length_eq_zero_iff.mpr (NumbersDVR.localizedQuot_subsingleton_of_not_le _ Wa hZW)]
      rfl
  have hL : NumbersDVR.divCycle P0 s W =
      ((NumbersDVR.multAt (P0 ⊔ Ideal.span {s}) W).toNat : ℤ) := by
    unfold NumbersDVR.divCycle
    rw [dif_pos (show W ∈ (P0 ⊔ Ideal.span {s}).minimalPrimes ∧ NumbersDVR.IsRelevant W from hW)]
  have hM : (extC P0).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  rw [hL, finsum_mem_congr rfl hterm, h1, h2]
  rw [h2] at hfin
  rw [finsum_mem_eq_finite_toFinset_sum _ hM] at hfin ⊢
  rw [ENat.toNat_sum fun Z hZ hZt => hfin (top_unique
    (hZt ▸ Finset.single_le_sum (fun _ _ => zero_le) hZ)), Nat.cast_sum,
    finsum_mem_eq_finite_toFinset_sum _ hM]

end

end GroundTheory.Heights₂.Heights.Inter
