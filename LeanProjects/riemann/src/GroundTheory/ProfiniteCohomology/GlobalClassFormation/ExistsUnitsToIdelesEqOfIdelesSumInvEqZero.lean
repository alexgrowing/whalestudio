import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ABHNPrep
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassSplit
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleRestriction.ExistsInfIdelesLocalResIdelesResFieldEqZeroOfInf
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

open scoped DirectSum GroundTheory.Global.SemiLocal

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

theorem idelesToClasses_idelesResField (K E : FiniteSubfield) [Fact (K ≤ E)] (y : cohomology (limitRep K) 2) :
    (idelesToClasses E 2).hom ((idelesResField K E 2).hom y) =
      (classResField K E 2).hom ((idelesToClasses K 2).hom y) := by
  have hc : cochainsMapAlong (fixingIncl K E) (continuous_fixingIncl K E) (idelesResMor K E) ≫
      cochainsMap (idelesShortComplexRes E).g =
      cochainsMap (idelesShortComplexRes K).g ≫
        cochainsMapAlong (fixingIncl K E) (continuous_fixingIncl K E) (classResMor K E) := by
    ext m x : 3
    apply Subtype.ext
    funext g
    rfl
  have e1 : idelesResField K E 2 ≫ idelesToClasses E 2 = HomologicalComplex.homologyMap
      (cochainsMapAlong (fixingIncl K E) (continuous_fixingIncl K E) (idelesResMor K E) ≫
        cochainsMap (idelesShortComplexRes E).g) 2 :=
    (HomologicalComplex.homologyMap_comp _ _ 2).symm
  have e2 : idelesToClasses K 2 ≫ classResField K E 2 = HomologicalComplex.homologyMap
      (cochainsMap (idelesShortComplexRes K).g ≫
        cochainsMapAlong (fixingIncl K E) (continuous_fixingIncl K E) (classResMor K E)) 2 :=
    (HomologicalComplex.homologyMap_comp _ _ 2).symm
  have h : idelesResField K E 2 ≫ idelesToClasses E 2 = idelesToClasses K 2 ≫ classResField K E 2 := by
    rw [e1, e2, hc]
    rfl
  exact congrArg (fun φ => φ.hom y) h

variable {K : FiniteSubfield} (ι : LocalEmbeddings K)

theorem idelesSumInv_eq_zero_of_idelesToClasses_eq_zero (w : cohomology (limitRep K) 2)
    (hw : (idelesToClasses K 2).hom w = 0) : idelesSumInv ι w = 0 := by
  obtain ⟨x, rfl⟩ := exists_unitsToIdeles_eq K 2 w hw
  exact idelesSumInv_unitsToIdeles ι x

theorem eq_zero_of_mk_div_eq_zero {k n : ℕ} (hk : k < n) (h : QZ.mk ((k : ℚ) / n) = 0) : k = 0 := by
  rw [QZ.mk_eq_zero_iff] at h
  obtain ⟨z, hz⟩ := h
  have hnpos : (0 : ℚ) < n := by exact_mod_cast (Nat.zero_le k).trans_lt hk
  have h1 : (z : ℚ) < 1 := by
    rw [hz, div_lt_one hnpos]
    exact_mod_cast hk
  have h2 : (0 : ℚ) ≤ z := by
    rw [hz]
    positivity
  have hz0 : z = 0 := by
    have h1' : z < 1 := by exact_mod_cast h1
    have h2' : 0 ≤ z := by exact_mod_cast h2
    omega
  rw [hz0, Int.cast_zero, eq_comm, div_eq_zero_iff] at hz
  rcases hz with hz | hz
  · exact_mod_cast hz
  · exact absurd hz hnpos.ne'

theorem exists_unitsToIdeles_eq_of_idelesSumInv_eq_zero (y : cohomology (limitRep K) 2)
    (hy : idelesSumInv ι y = 0) : ∃ x, (unitsToIdeles K 2).hom x = y := by
  classical
  obtain ⟨a₀, ha₀⟩ := exists_sub_unitsToIdeles_iChar_inl_eq_zero ι y
  set y' := y - (unitsToIdeles K 2).hom (globalCupClass (iChar K) a₀) with hy'def
  have hy' : idelesSumInv ι y' = 0 := by
    rw [hy'def, map_sub, hy, idelesSumInv_unitsToIdeles, sub_zero]
  suffices h : ∃ x, (unitsToIdeles K 2).hom x = y' by
    obtain ⟨x, hx⟩ := h
    exact ⟨x + globalCupClass (iChar K) a₀, by rw [map_add, hx, hy'def, sub_add_cancel]⟩
  obtain ⟨m, hm0, hm⟩ := exists_nsmul_eq_zero_limitRep y'
  let S : Finset (HeightOneSpectrum (𝓞 K.1)) :=
    (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y').support.preimage Sum.inr Sum.inr_injective.injOn
  obtain ⟨E, _, hgal, hcyc, -, hdeg⟩ := CyclotomicLayer.exists_cyclic_layer_dvd_localDegree K S hm0
  have hres : (idelesResField K E 2).hom y' = 0 := by
    refine idelesResField_eq_zero ι y' ha₀ fun v w => ?_
    by_cases hv : v ∈ S
    · obtain ⟨k, hk⟩ := hdeg v hv w
      rw [hk, mul_comm, mul_smul]
      have h0 : m • placeInv (K := K) (.inr v) (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y' (.inr v)) = 0 := by
        rw [← map_nsmul, ← DFinsupp.smul_apply, ← map_nsmul, hm, map_zero]
        exact map_zero _
      rw [h0, smul_zero]
    · have h0 : idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y' (.inr v) = 0 := by
        by_contra h
        exact hv (by rw [Finset.mem_preimage, DFinsupp.mem_support_iff]; exact h)
      rw [h0, map_zero, smul_zero]
  obtain ⟨Z, hZ, hZinf, hZfin⟩ := exists_idelesSumInv_eq_one_div ι E
  have hresZ : (idelesResField K E 2).hom Z = 0 := idelesResField_eq_zero ι Z hZinf hZfin
  set n := Module.finrank K.1 E.1 with hn
  have hn0 : n ≠ 0 := Module.finrank_pos.ne'
  have hM : Nat.card (LinearMap.ker (classResField K E 2).hom) = n := natCard_ker_classResField_of_isCyclic K E
  have hmemM : ∀ w : cohomology (limitRep K) 2, (idelesResField K E 2).hom w = 0 →
      (idelesToClasses K 2).hom w ∈ LinearMap.ker (classResField K E 2).hom := by
    intro w hw
    rw [LinearMap.mem_ker, ← idelesToClasses_idelesResField, hw, map_zero]
  have hT : ∀ k : ℕ, idelesSumInv ι (k • Z) = QZ.mk ((k : ℚ) / n) := by
    intro k
    rw [map_nsmul, hZ, ← QZ.mk_nsmul, nsmul_eq_mul, mul_one_div]
  let f : Fin n → LinearMap.ker (classResField K E 2).hom := fun k =>
    ⟨(idelesToClasses K 2).hom ((k : ℕ) • Z), hmemM _ (by rw [map_nsmul, hresZ, smul_zero])⟩
  have finj : Function.Injective f := by
    intro k k' hkk
    have h1 : (idelesToClasses K 2).hom ((k : ℕ) • Z) = (idelesToClasses K 2).hom ((k' : ℕ) • Z) :=
      congrArg Subtype.val hkk
    have key : ∀ a b : Fin n, (b : ℕ) ≤ a →
        (idelesToClasses K 2).hom ((a : ℕ) • Z) = (idelesToClasses K 2).hom ((b : ℕ) • Z) → a = b := by
      intro a b hba hab
      have hw : (idelesToClasses K 2).hom (((a : ℕ) - b) • Z) = 0 := by
        rw [sub_nsmul _ hba, ← sub_eq_add_neg, map_sub, hab, sub_self]
      have h2 := idelesSumInv_eq_zero_of_idelesToClasses_eq_zero ι _ hw
      rw [hT] at h2
      have := eq_zero_of_mk_div_eq_zero (lt_of_le_of_lt (Nat.sub_le _ _) a.2) (by exact_mod_cast h2)
      exact Fin.ext (by omega)
    rcases le_total (k' : ℕ) k with h | h
    · exact key k k' h h1
    · exact (key k' k h h1.symm).symm
  have : Finite (LinearMap.ker (classResField K E 2).hom) := Nat.finite_of_card_ne_zero (hM ▸ hn0)
  have fsurj := (finj.bijective_of_nat_card_le (by rw [hM, Nat.card_eq_fintype_card, Fintype.card_fin])).2
  obtain ⟨k, hk⟩ := fsurj ⟨(idelesToClasses K 2).hom y', hmemM y' hres⟩
  have hk' : (idelesToClasses K 2).hom (y' - (k : ℕ) • Z) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact (congrArg Subtype.val hk).symm
  have h2 := idelesSumInv_eq_zero_of_idelesToClasses_eq_zero ι _ hk'
  rw [map_sub, hy', hT, zero_sub, neg_eq_zero] at h2
  have hk0 : (k : ℕ) = 0 := eq_zero_of_mk_div_eq_zero k.2 h2
  rw [hk0, zero_smul, sub_zero] at hk'
  exact exists_unitsToIdeles_eq K 2 y' hk'

theorem sumPlaceInv_eq_zero_iff (y : ⨁ v : Place K.1, localGaloisCohomology K 2 v) :
    sumPlaceInv K y = 0 ↔ ∃ x, brauerLocal ι x = y := by
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := exists_unitsToIdeles_eq_of_idelesSumInv_eq_zero ι
      ((idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm y) (by
        rw [idelesSumInv_apply, AddEquiv.apply_symm_apply, hy])
    exact ⟨x, by rw [brauerLocal_apply, hx, AddEquiv.apply_symm_apply]⟩
  · rintro ⟨x, rfl⟩
    exact brauerSumInv_eq_zero ι x

theorem albertBrauerHasseNoether :
    Function.Injective (brauerLocal ι) ∧
      (∀ y : ⨁ v : Place K.1, localGaloisCohomology K 2 v, sumPlaceInv K y = 0 ↔ ∃ x, brauerLocal ι x = y) ∧
      Function.Surjective (sumPlaceInv K) :=
  ⟨brauerLocal_injective ι, sumPlaceInv_eq_zero_iff ι, sumPlaceInv_surjective K⟩

end

end GroundTheory.ProfCoh
