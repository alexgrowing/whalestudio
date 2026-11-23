import Mathlib
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassFieldLocal
import GroundTheory.GlobalFields.ClassFieldConsequences.IdealRayClass
import GroundTheory.GlobalFields.ClassFieldConsequences.OpenSubgroup
import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
import GroundTheory.GlobalFields.GlobalArtinMap.ArtinMap

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup SemiLocal WithZero
open GroundTheory.LocalField (restrictAb le_maximalAbelianExtension)
open scoped Pointwise

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

namespace Modulus

variable (𝔪 : Modulus K)

def normSubgroup : OpenFiniteIndexSubgroup K :=
  ⟨𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K), 𝔪.isOpen_map_congruenceSubgroup,
    𝔪.finiteIndex_map_congruenceSubgroup⟩

theorem finiteEmbedding_mem_congruenceSubgroup {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔪.ideal) {u : (v.adicCompletion K)ˣ}
    (hu : Valued.v (u : v.adicCompletion K) = 1) :
    finiteEmbedding v u ∈ 𝔪.congruenceSubgroup := by
  refine 𝔪.mem_congruenceSubgroup.2 ⟨fun w ↦ ?_, fun w _ ↦ ?_⟩
  · by_cases hwv : w = v
    · subst hwv
      rw [finiteProj_finiteEmbedding, (𝔪.exponent_eq_zero_iff w).2 hv]
      refine mem_unitsLevel.2 ⟨hu, ?_⟩
      rw [Nat.cast_zero, neg_zero, exp_zero]
      exact Valuation.map_sub_le _ hu.le (by simp)
    · rw [finiteProj_finiteEmbedding_of_ne hwv]
      exact one_mem _
  · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (1 : w.1.Completion)
    rw [map_one]
    exact one_pos

theorem exists_uniformizer_finiteEmbedding_mem_idelesOneMod {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔪.ideal) :
    ∃ π : (v.adicCompletion K)ˣ, LocalField.ord (π : v.adicCompletion K) = 1 ∧
      ∃ _ : finiteEmbedding v π ∈ 𝔪.idelesOneMod,
        toFractionalIdeal (finiteEmbedding v π) = primeIdealUnit v := by
  classical
  obtain ⟨π, hπ, hval⟩ := exists_ord_eq_one_valued v
  refine ⟨π, hπ, 𝔪.mem_idelesOneMod.2 ⟨fun w hw ↦ ?_, fun w _ ↦ ?_⟩,
    toFractionalIdeal_eq_iff.2 fun w ↦ ?_⟩
  · have hwv : w ≠ v := fun h ↦ hv (h ▸ hw)
    rw [finiteProj_finiteEmbedding_of_ne hwv]
    exact one_mem _
  · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (1 : w.1.Completion)
    rw [map_one]
    exact one_pos
  · rw [count_primeIdealUnit]
    split_ifs with h
    · subst h
      rw [ord_finiteEmbedding_self, hval, log_exp, neg_neg]
    · exact ord_finiteEmbedding_of_ne h _

theorem primeIdealUnit_mem_coprimeIdeals {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal) :
    primeIdealUnit v ∈ 𝔪.coprimeIdeals := fun w hw ↦ by
  rw [count_primeIdealUnit, if_neg]
  rintro rfl
  exact hv hw

def primeClass {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal) : 𝔪.IdealRayClassGroup :=
  QuotientGroup.mk ⟨primeIdealUnit v, 𝔪.primeIdealUnit_mem_coprimeIdeals hv⟩

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

def rayClassFieldSubfield : FiniteAbelianSubfield K Ω :=
  (normGroupOrderIso K Ω).symm (OrderDual.toDual 𝔪.normSubgroup)

def rayClassField : IntermediateField K Ω :=
  (𝔪.rayClassFieldSubfield Ω).1

instance finiteDimensional_rayClassField : FiniteDimensional K (𝔪.rayClassField Ω) :=
  (𝔪.rayClassFieldSubfield Ω).2.1

instance isAbelianGalois_rayClassField : IsAbelianGalois K (𝔪.rayClassField Ω) :=
  (𝔪.rayClassFieldSubfield Ω).2.2

theorem range_ideleClassNorm_rayClassField :
    (ideleClassNorm K (𝔪.rayClassField Ω)).range = 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) := by
  have h : normGroup (𝔪.rayClassFieldSubfield Ω) = 𝔪.normSubgroup := by
    rw [← normGroupOrderIso_apply, rayClassFieldSubfield, OrderIso.apply_symm_apply]
    rfl
  exact congrArg Subtype.val h

def rayClassGroupGalEquiv : 𝔪.RayClassGroup ≃* (𝔪.rayClassField Ω ≃ₐ[K] 𝔪.rayClassField Ω) :=
  𝔪.quotientMapCongruenceEquiv.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (𝔪.range_ideleClassNorm_rayClassField Ω).symm).trans
      (reciprocityMapEquiv K (𝔪.rayClassField Ω)))

theorem rayClassGroupGalEquiv_mk (x : IdeleGroup K) :
    𝔪.rayClassGroupGalEquiv Ω (QuotientGroup.mk x) =
      reciprocityMap K (𝔪.rayClassField Ω) (IdeleClassGroup.mk K x) := by
  rw [rayClassGroupGalEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply,
    ← quotientMapCongruenceEquiv_mk, MulEquiv.symm_apply_apply]
  rfl

def rayClassArtinEquiv : 𝔪.IdealRayClassGroup ≃* (𝔪.rayClassField Ω ≃ₐ[K] 𝔪.rayClassField Ω) :=
  𝔪.rayClassGroupEquiv.symm.trans (𝔪.rayClassGroupGalEquiv Ω)

theorem rayClassArtinEquiv_mk {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod) :
    𝔪.rayClassArtinEquiv Ω (QuotientGroup.mk ⟨toFractionalIdeal x,
      𝔪.toFractionalIdeal_mem_coprimeIdeals hx⟩) =
      reciprocityMap K (𝔪.rayClassField Ω) (IdeleClassGroup.mk K x) := by
  rw [rayClassArtinEquiv, MulEquiv.trans_apply, ← 𝔪.rayClassGroupEquiv_mk hx,
    MulEquiv.symm_apply_apply, rayClassGroupGalEquiv_mk]

theorem unitFiltrationUnits_le_ker_localSymbol {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal) :
    LocalField.unitFiltrationUnits (v.adicCompletion K) 0 ≤ (localSymbol (𝔪.rayClassField Ω) v).ker := by
  intro u hu
  have hx : IdeleClassGroup.mk K (finiteEmbedding v u) ∈
      (ideleClassNorm K (𝔪.rayClassField Ω)).range := by
    rw [𝔪.range_ideleClassNorm_rayClassField Ω]
    exact ⟨_, 𝔪.finiteEmbedding_mem_congruenceSubgroup hv
      (mem_unitFiltrationUnits_zero_iff_valued.1 hu), rfl⟩
  rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_mk, ideleSymbol_finiteEmbedding] at hx
  exact hx

theorem ramificationIdx_rayClassField_eq_one {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal)
    (w : HeightOneSpectrum (𝓞 (𝔪.rayClassField Ω))) [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
  ramificationIdx_eq_one_of_units_le_ker_localSymbol v (𝔪.unitFiltrationUnits_le_ker_localSymbol Ω hv) w

theorem rayClassArtinEquiv_primeClass {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal)
    (w : HeightOneSpectrum (𝓞 (𝔪.rayClassField Ω))) [w.asIdeal.LiesOver v.asIdeal] :
    𝔪.rayClassArtinEquiv Ω (𝔪.primeClass hv) =
      arithFrobAt (𝓞 K) (𝔪.rayClassField Ω ≃ₐ[K] 𝔪.rayClassField Ω) w.asIdeal := by
  obtain ⟨π, hπ, hx, hxp⟩ := 𝔪.exists_uniformizer_finiteEmbedding_mem_idelesOneMod hv
  have hc : 𝔪.primeClass hv = QuotientGroup.mk ⟨toFractionalIdeal (finiteEmbedding v π),
      𝔪.toFractionalIdeal_mem_coprimeIdeals hx⟩ := by
    rw [primeClass]
    congr 2
    exact hxp.symm
  rw [hc, 𝔪.rayClassArtinEquiv_mk Ω hx, reciprocityMap_mk,
    ideleSymbol_finiteEmbedding_eq_arithFrobAt v w (𝔪.ramificationIdx_rayClassField_eq_one Ω hv w) hπ]

theorem splitsCompletely_rayClassField_iff {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal) :
    SplitsCompletely (𝔪.rayClassField Ω) v ↔ 𝔪.primeClass hv = 1 := by
  obtain ⟨w, hw⟩ := nonempty_placesOver (𝔪.rayClassField Ω) v
  rw [splitsCompletely_iff_arithFrobAt_eq_one v (𝔪.unitFiltrationUnits_le_ker_localSymbol Ω hv) w,
    ← 𝔪.rayClassArtinEquiv_primeClass Ω hv w, MulEquiv.map_eq_one_iff]

end Modulus

theorem exists_le_rayClassField (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L] :
    ∃ 𝔪 : Modulus K, L ≤ 𝔪.rayClassField Ω := by
  obtain ⟨𝔪, -, hle⟩ := IdeleClassGroup.exists_map_congruenceSubgroup_le _
    (isOpen_range_ideleClassNorm (K := K) (L := L))
  refine ⟨𝔪, (range_ideleClassNorm_le_range_iff L (𝔪.rayClassField Ω)).1 ?_⟩
  rw [𝔪.range_ideleClassNorm_rayClassField Ω]
  exact hle

end

end GroundTheory.Global
