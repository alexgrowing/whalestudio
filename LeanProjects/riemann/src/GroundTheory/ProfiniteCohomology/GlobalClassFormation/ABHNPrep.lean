import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.SumInvariants
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalDegreeGen
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassSplit
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

open scoped DirectSum GroundTheory.Global.SemiLocal

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (ι : LocalEmbeddings K)

def idelesSumInv : cohomology (limitRep K) 2 →+ QZ :=
  (sumPlaceInv K).comp (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).toAddMonoidHom

theorem idelesSumInv_apply (y : cohomology (limitRep K) 2) :
    idelesSumInv ι y = sumPlaceInv K (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y) :=
  rfl

theorem idelesSumInv_unitsToIdeles (x : cohomology (unitsLimitRep K) 2) :
    idelesSumInv ι ((unitsToIdeles K 2).hom x) = 0 :=
  brauerSumInv_eq_zero ι x

variable (K) in

theorem sumPlaceInv_surjective : Function.Surjective (sumPlaceInv K) := by
  classical
  intro q
  obtain ⟨v⟩ := nonempty_heightOneSpectrum K.1
  obtain ⟨t, ht⟩ := (placeInv_bijective_inr (K := K) v).2 q
  exact ⟨DirectSum.of _ (.inr v) t, by rw [sumPlaceInv_of, ht]⟩

theorem exists_nsmul_eq_zero_limitRep (y : cohomology (limitRep K) 2) : ∃ m : ℕ, m ≠ 0 ∧ m • y = 0 := by
  obtain ⟨p, z, rfl⟩ := exists_levelInfl_eq 2 y
  refine ⟨Fintype.card (p.1.1 ≃ₐ[K.1] p.1.1), Fintype.card_ne_zero, ?_⟩
  rw [← map_nsmul]
  have h := card_smul_groupCohomology (ideleRep K.1 p.1.1) two_ne_zero
    ((cohomologyIsoGroupCohomology _ 2).hom.hom z)
  have hz : Fintype.card (p.1.1 ≃ₐ[K.1] p.1.1) • z = 0 := by
    apply (ModuleCat.mono_iff_injective (cohomologyIsoGroupCohomology (ideleRep K.1 p.1.1) 2).hom).1
      inferInstance
    rw [map_nsmul, h, map_zero]
  rw [hz, map_zero]

theorem exists_sub_unitsToIdeles_iChar_inl_eq_zero (y : cohomology (limitRep K) 2) :
    ∃ a : K.1ˣ, ∀ v : InfinitePlace K.1, idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)
      (y - (unitsToIdeles K 2).hom (globalCupClass (iChar K) a)) (.inl v) = 0 := by
  classical
  obtain ⟨a, ha⟩ := exists_units_neg_iff (L := K.1)
    fun v => decide (placeInv (K := K) (.inl v.1)
      (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y (.inl v.1)) ≠ 0)
  refine ⟨a, fun v => ?_⟩
  rw [map_sub, DFinsupp.sub_apply]
  change _ - brauerLocal ι (globalCupClass (iChar K) a) (.inl v) = 0
  by_cases hv : v.IsReal
  · apply placeInv_injective (.inl v)
    rw [map_sub, map_zero, sub_eq_zero, placeInv_brauerLocal_globalCupClass_iChar, dif_pos hv]
    have hs := ha ⟨v, hv⟩
    simp only [decide_eq_true_eq] at hs
    rcases placeInv_inl_eq_zero_or_eq_half v (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y (.inl v))
      with h | h
    · rw [if_neg (fun hneg => (hs.1 hneg) h), h]
    · rw [if_pos (hs.2 (by rw [h]; exact QZ.mk_half_ne_zero)), h]
  · have := subsingleton_cohomology_two_of_isComplex v (InfinitePlace.not_isReal_iff_isComplex.1 hv)
    exact Subsingleton.elim (α := cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) _ _

section Generator

variable (E : FiniteSubfield) [Fact (K ≤ E)] [IsGalois K.1 E.1] [IsCyclic Gal(E.1/K.1)]

def QZ.mkHom : ℚ →+ QZ where
  toFun := QZ.mk
  map_zero' := QZ.mk_zero
  map_add' := QZ.mk_add

theorem exists_idelesSumInv_eq_one_div :
    ∃ Z : cohomology (limitRep K) 2, idelesSumInv ι Z = QZ.mk (1 / Module.finrank K.1 E.1) ∧
      (∀ v : InfinitePlace K.1, idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) Z (.inl v) = 0) ∧
      ∀ (v : HeightOneSpectrum (𝓞 K.1)) (w : SemiLocal.PlacesOver E.1 v),
        Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion E.1) •
          placeInv (.inr v) (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) Z (.inr v)) = 0 := by
  classical
  obtain ⟨s, c, hsd, hsum⟩ := exists_sum_mul_div_localDegree_eq_one E (K := K)
  have ht : ∀ v : HeightOneSpectrum (𝓞 K.1), ∃ t : localGaloisCohomology K 2 (.inr v),
      placeInv (.inr v) t = QZ.mk (c v / localDegree E v) := fun v =>
    (placeInv_bijective_inr (K := K) v).2 _
  choose t ht using ht
  let D : ⨁ u : Place K.1, localGaloisCohomology K 2 u := ∑ u ∈ s, DirectSum.of _ (.inr u) (t u)
  refine ⟨(idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm D, ?_, fun v => ?_, fun v w => ?_⟩
  · rw [idelesSumInv_apply, AddEquiv.apply_symm_apply, map_sum]
    simp_rw [sumPlaceInv_of, ht]
    change ∑ u ∈ s, QZ.mkHom (c u / localDegree E u) = _
    rw [← map_sum]
    change QZ.mk _ = _
    congr 1
    have hn0 : (Module.finrank K.1 E.1 : ℚ) ≠ 0 := by
      exact_mod_cast (Module.finrank_pos (R := K.1) (M := E.1)).ne'
    have hdu : ∀ u ∈ s, (c u / localDegree E u : ℚ) =
        (c u : ℚ) * (((Module.finrank K.1 E.1 / localDegree E u : ℕ) : ℤ) : ℚ) / Module.finrank K.1 E.1 := by
      intro u hu
      have hd0 : (localDegree E u : ℚ) ≠ 0 := by
        have := Nat.pos_of_dvd_of_pos (hsd u hu) (Module.finrank_pos (R := K.1) (M := E.1))
        exact_mod_cast (Nat.pos_of_ne_zero (fun h => by rw [h] at this; exact (lt_irrefl 0 this))).ne'
      rw [Int.cast_natCast, Nat.cast_div (hsd u hu) hd0]
      field_simp
    have hsumQ : (∑ u ∈ s, (c u : ℚ) * (((Module.finrank K.1 E.1 / localDegree E u : ℕ) : ℤ) : ℚ)) = 1 := by
      exact_mod_cast hsum
    rw [Finset.sum_congr rfl hdu, ← Finset.sum_div, hsumQ]
  · rw [AddEquiv.apply_symm_apply, DFinsupp.finsetSum_apply]
    exact Finset.sum_eq_zero fun u _ => DirectSum.of_eq_of_ne _ _ _ (by simp)
  · rw [AddEquiv.apply_symm_apply, DFinsupp.finsetSum_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_eq_zero fun u hu => ?_
    by_cases huv : u = v
    · subst huv
      rw [DirectSum.of_eq_same, ht, finrank_eq_localDegree, ← QZ.mk_nsmul]
      rw [QZ.mk_eq_zero_iff]
      refine ⟨c u, ?_⟩
      have hd0 : (localDegree E u : ℚ) ≠ 0 := by
        have := Nat.pos_of_dvd_of_pos (hsd u hu) (Module.finrank_pos (R := K.1) (M := E.1))
        exact_mod_cast this.ne'
      rw [nsmul_eq_mul]
      field_simp
    · rw [DirectSum.of_eq_of_ne _ _ _ (by simpa using Ne.symm huv), map_zero, smul_zero]

end Generator

end

end GroundTheory.ProfCoh
