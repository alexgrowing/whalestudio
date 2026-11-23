import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.SignsCup
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.SymbolBridgeCyclotomic
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.EqZeroOfBrauerLocalApplyEqZero
import GroundTheory.GlobalFields.NormResidueSymbol.CyclotomicCompositum
import GroundTheory.GlobalFields.NormResidueSymbol.Rational
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

open scoped DirectSum NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

theorem subsingleton_cohomology_two_of_isComplex (v : InfinitePlace K.1) (hv : v.IsComplex) :
    Subsingleton (cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) := by
  obtain ⟨F, _, w, ⟨e⟩⟩ := exists_infCompletion_algEquiv v
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  have h1 : Module.finrank v.Completion (AlgebraicClosure v.Completion) = 1 := by
    rw [← e.toLinearEquiv.finrank_eq]
    exact (InfinitePlace.finrank_completion_eq_one_iff (w : InfinitePlace F.1)).2
      fun h => (InfinitePlace.not_isReal_iff_isComplex.2 hv) h.1
  have hcard : Nat.card Gal(AlgebraicClosure v.Completion/v.Completion) = 1 := by
    rw [IsGalois.card_aut_eq_finrank, h1]
  have : Subsingleton Gal(AlgebraicClosure v.Completion/v.Completion) :=
    (Nat.card_eq_one_iff_unique.1 hcard).1
  have : DiscreteTopology Gal(AlgebraicClosure v.Completion/v.Completion) := inferInstance
  exact ModuleCat.isZero_iff_subsingleton.1
    ((isZero_groupCohomology_succ_of_subsingleton _ 1).of_iso (cohomologyIsoGroupCohomology _ 2))

theorem placeInv_inl_eq_zero_or_eq_half (v : InfinitePlace K.1) (t : localGaloisCohomology K 2 (.inl v)) :
    placeInv (.inl v) t = 0 ∨ placeInv (.inl v) t = QZ.mk (1 / 2) := by
  by_cases ht : t = 0
  · left
    rw [ht, map_zero]
  · right
    exact quadraticInvFun_of_ne_zero _ _ ht

def gaussField : FiniteSubfield :=
  ⟨Cyclotomic.rootsOfUnityField 4, IsCyclotomicExtension.finiteDimensional {4} ℚ _⟩

theorem sqrtNegOne_mem_gaussField : sqrtNegOne ∈ gaussField.1 :=
  IntermediateField.subset_adjoin ℚ _ (show sqrtNegOne ^ 4 = 1 by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sqrtNegOne_sq]; norm_num)

variable (ι : LocalEmbeddings K)

theorem brauerSumInv_globalCupClass_iChar (a : K.1ˣ) : brauerSumInv ι (globalCupClass (iChar K) a) = 0 := by
  have : IsCyclotomicExtension {4} ℚ gaussField.1 :=
    (inferInstance : IsCyclotomicExtension {4} ℚ (Cyclotomic.rootsOfUnityField 4))
  have : IsGalois ℚ gaussField.1 := IsCyclotomicExtension.isGalois {4} ℚ gaussField.1
  have : IsMulCommutative (gaussField.1 ≃ₐ[ℚ] gaussField.1) :=
    IsCyclotomicExtension.isMulCommutative {4} ℚ gaussField.1
  rw [brauerSumInv_globalCupClass]
  refine finsum_char_localSymbolAt_eq_zero (CyclotomicSymbol.compositum K gaussField) ι
    (sup_le_sup_left (RationalSymbol.rootsOfUnityField_le_maxCyclotomic 4) K.1) (iChar K) (fun h hh => ?_) a
  apply iChar_apply_of_fix
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh _
    ((show gaussField.1 ≤ (CyclotomicSymbol.compositum K gaussField).1 from le_sup_right)
      sqrtNegOne_mem_gaussField)

theorem exists_brauerLocal_sub_globalCupClass_iChar_inl_eq_zero (x : cohomology (unitsLimitRep K) 2) :
    ∃ a : K.1ˣ, ∀ v : InfinitePlace K.1,
      brauerLocal ι (x - globalCupClass (iChar K) a) (.inl v) = 0 := by
  classical
  obtain ⟨a, ha⟩ := exists_units_neg_iff (L := K.1)
    fun v => decide (placeInv (K := K) (.inl v.1) (brauerLocal ι x (.inl v.1)) ≠ 0)
  refine ⟨a, fun v => ?_⟩
  rw [map_sub, DFinsupp.sub_apply]
  by_cases hv : v.IsReal
  · apply placeInv_injective (.inl v)
    rw [map_sub, map_zero, sub_eq_zero, placeInv_brauerLocal_globalCupClass_iChar, dif_pos hv]
    have hs := ha ⟨v, hv⟩
    simp only [decide_eq_true_eq] at hs
    rcases placeInv_inl_eq_zero_or_eq_half v (brauerLocal ι x (.inl v)) with h | h
    · rw [if_neg (fun hneg => (hs.1 hneg) h), h]
    · rw [if_pos (hs.2 (by rw [h]; exact QZ.mk_half_ne_zero)), h]
  · have := subsingleton_cohomology_two_of_isComplex v (InfinitePlace.not_isReal_iff_isComplex.1 hv)
    exact Subsingleton.elim (α := cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) _ _

end

end GroundTheory.ProfCoh
