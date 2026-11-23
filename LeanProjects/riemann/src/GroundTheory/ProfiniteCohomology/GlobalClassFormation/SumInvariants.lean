import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.CupDecompositionGlobal
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.Splitting
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.RealPlaces
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.UnitsLevels
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalDegrees
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

open scoped DirectSum GroundTheory.Global.SemiLocal

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (ι : LocalEmbeddings K)

theorem exists_nsmul_eq_zero_unitsLimitRep (x : cohomology (unitsLimitRep K) 2) : ∃ m : ℕ, m ≠ 0 ∧ m • x = 0 := by
  obtain ⟨p, y, rfl⟩ := exists_unitsLevelInfl_eq 2 x
  refine ⟨Fintype.card (p.1.1 ≃ₐ[K.1] p.1.1), Fintype.card_ne_zero, ?_⟩
  rw [← map_nsmul]
  have h := card_smul_groupCohomology (galUnitsZ K.1 p.1.1) two_ne_zero
    ((cohomologyIsoGroupCohomology _ 2).hom.hom y)
  have hy : Fintype.card (p.1.1 ≃ₐ[K.1] p.1.1) • y = 0 := by
    apply (ModuleCat.mono_iff_injective (cohomologyIsoGroupCohomology (galUnitsZ K.1 p.1.1) 2).hom).1
      inferInstance
    rw [map_nsmul, h, map_zero]
  rw [hy, map_zero]

theorem brauerSumInv_eq_zero (x : cohomology (unitsLimitRep K) 2) : brauerSumInv ι x = 0 := by
  classical
  obtain ⟨a₀, ha₀⟩ := exists_brauerLocal_sub_globalCupClass_iChar_inl_eq_zero ι x
  set x' := x - globalCupClass (iChar K) a₀ with hx'
  obtain ⟨m, hm0, hm⟩ := exists_nsmul_eq_zero_unitsLimitRep x'
  let S : Finset (HeightOneSpectrum (𝓞 K.1)) :=
    (brauerLocal ι x').support.preimage Sum.inr Sum.inr_injective.injOn
  obtain ⟨E, _, hgal, hcyc, hEle, hdeg⟩ := CyclotomicLayer.exists_cyclic_layer_dvd_localDegree K S hm0
  have hsplit : (unitsResField K E 2).hom x' = 0 :=
    unitsResField_eq_zero_of_dvd_finrank ι x' m hm ha₀ fun v hv w => hdeg v (by
      rw [Finset.mem_preimage, DFinsupp.mem_support_iff]
      exact hv) w
  obtain ⟨χ, b, hχ, hb⟩ := exists_globalCupClass_eq_of_unitsResField_eq_zero x' hsplit
  have : (E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal := normal_subgroupOf_of_isGalois (K := K) (E := E)
  have : IsMulCommutative (E.1 ≃ₐ[K.1] E.1) := by
    let := IsCyclic.commGroup (α := E.1 ≃ₐ[K.1] E.1)
    exact ⟨⟨fun a c => mul_comm a c⟩⟩
  have h' : brauerSumInv ι x' = 0 := by
    rw [← hb, brauerSumInv_globalCupClass]
    exact finsum_char_localSymbolAt_eq_zero E ι (hEle.trans (sup_le_sup_left Cyclotomic.zhatField_le_maxCyclotomic _))
      χ hχ b
  have hx : x = x' + globalCupClass (iChar K) a₀ := by rw [hx', sub_add_cancel]
  rw [hx, map_add, h', brauerSumInv_globalCupClass_iChar, add_zero]

end

end GroundTheory.ProfCoh
