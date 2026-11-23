import Mathlib
import GroundTheory.LocalFields.Examples
import GroundTheory.LocalFields.Interface
import GroundTheory.LocalFields.Uniqueness
import GroundTheory.LocalFields.FiniteExtension
import GroundTheory.LocalFields.DifferentGalois
import GroundTheory.LocalFields.UpperNumbering
import GroundTheory.PAdicHodge.PerfectoidField
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open ValuativeRel

variable {p : ℕ} [Fact p.Prime]

section Subfield

variable {S : Type*} [SetLike S (PadicAlgCl p)] [SubfieldClass S (PadicAlgCl p)] (s : S)

instance subfield_isUltrametricDist : IsUltrametricDist s :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y =>
    (PadicAlgCl.isNonarchimedean p) (x : PadicAlgCl p) y

instance subfield_valuativeRel : ValuativeRel s :=
  ValuativeRel.ofValuation (NormedField.valuation (K := s))

theorem subfield_norm_def (x : s) : ‖x‖ = ‖(x : PadicAlgCl p)‖ := rfl

theorem subfield_vle_iff_norm_le (x y : s) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  change NormedField.valuation x ≤ NormedField.valuation y ↔ _
  exact NNReal.coe_le_coe

instance subfield_compatible : (NormedField.valuation (K := s)).Compatible :=
  Valuation.Compatible.ofValuation _

instance subfield_isValuativeTopology : IsValuativeTopology s := by
  let : Valued s NNReal := NormedField.toValued
  have : (Valued.v : Valuation s NNReal).Compatible := subfield_compatible s
  exact GroundTheory.LocalField.isValuativeTopology_of_valued

theorem subfield_norm_natCast_prime : ‖((p : ℕ) : s)‖ = (p : ℝ)⁻¹ := by
  rw [subfield_norm_def]
  have h := PadicAlgCl.valuation_coe p (p : PadicAlgCl p)
  rw [PadicAlgCl.valuation_p] at h
  push_cast [map_natCast] at h ⊢
  rw [← h]
  simp

instance subfield_isNontrivial : IsNontrivial s := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine ⟨⟨valuation s (p : s), ?_, ?_⟩⟩
  · rw [ne_eq, Valuation.zero_iff]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  · intro h
    have h2 : (1 : s) ≤ᵥ ((p : ℕ) : s) := by
      rw [Valuation.vle_iff_le (valuation s), h, map_one]
    rw [subfield_vle_iff_norm_le, subfield_norm_natCast_prime, norm_one] at h2
    exact absurd h2 (not_le.2 (inv_lt_one_of_one_lt₀ hp))

theorem integer_eq_normInteger : 𝒪[s] = normInteger s := by
  ext x
  rw [Valuation.mem_integer_iff, mem_normInteger, ← map_one (valuation s),
    ← Valuation.vle_iff_le, subfield_vle_iff_norm_le, norm_one]

end Subfield

theorem locallyCompactSpace_of_finiteDimensional (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] : LocallyCompactSpace K := by
  let M := Subalgebra.toSubmodule K.toSubalgebra
  have : FiniteDimensional ℚ_[p] M := (inferInstance : FiniteDimensional ℚ_[p] K)
  have : ProperSpace M := FiniteDimensional.proper ℚ_[p] M
  exact (inferInstance : LocallyCompactSpace M)

theorem isNonarchimedeanLocalField_of_coe_eq {S : Type*} [SetLike S (PadicAlgCl p)]
    [SubfieldClass S (PadicAlgCl p)] (s : S) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (h : (s : Set (PadicAlgCl p)) = K) :
    IsNonarchimedeanLocalField s := by
  have : LocallyCompactSpace (K : Set (PadicAlgCl p)) := locallyCompactSpace_of_finiteDimensional K
  have : LocallyCompactSpace s := (Homeomorph.setCongr h).isClosedEmbedding.locallyCompactSpace
  exact {}

instance isNonarchimedeanLocalField_intermediateField (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] : IsNonarchimedeanLocalField K :=
  isNonarchimedeanLocalField_of_coe_eq K K rfl

instance finiteDimensional_tower (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (L : IntermediateField K (PadicAlgCl p)) [FiniteDimensional K L] :
    FiniteDimensional ℚ_[p] L :=
  Module.Finite.trans K L

instance isNonarchimedeanLocalField_tower (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (L : IntermediateField K (PadicAlgCl p)) [FiniteDimensional K L] :
    IsNonarchimedeanLocalField L :=
  have : FiniteDimensional ℚ_[p] (L.restrictScalars ℚ_[p]) :=
    (inferInstance : FiniteDimensional ℚ_[p] L)
  isNonarchimedeanLocalField_of_coe_eq L (L.restrictScalars ℚ_[p]) rfl

instance valuativeExtension_padic (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    ValuativeExtension ℚ_[p] K := by
  refine ⟨fun a b => ?_⟩
  rw [subfield_vle_iff_norm_le, subfield_norm_def, subfield_norm_def,
    IntermediateField.coe_algebraMap_apply, IntermediateField.coe_algebraMap_apply]
  have ha : ‖algebraMap ℚ_[p] (PadicAlgCl p) a‖ = ‖a‖ := PadicAlgCl.norm_extends p a
  have hb : ‖algebraMap ℚ_[p] (PadicAlgCl p) b‖ = ‖b‖ := PadicAlgCl.norm_extends p b
  rw [ha, hb, Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le]

instance valuativeExtension_intermediateField {F : Type*} [Field F] [Algebra F (PadicAlgCl p)]
    (E : IntermediateField F (PadicAlgCl p)) (L : IntermediateField E (PadicAlgCl p)) :
    ValuativeExtension E L :=
  ⟨fun a b => by rw [subfield_vle_iff_norm_le, subfield_vle_iff_norm_le]; rfl⟩

section Unique

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]

end Unique

section Inclusion

variable {K L : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L)

theorem valuativeExtension_inclusion :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    ValuativeExtension K L := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact ⟨fun a b => by rw [subfield_vle_iff_norm_le, subfield_vle_iff_norm_le]; rfl⟩

theorem isScalarTower_inclusion :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    IsScalarTower ℚ_[p] K L := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem finiteDimensional_inclusion [FiniteDimensional ℚ_[p] L] :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    FiniteDimensional K L := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have := isScalarTower_inclusion h
  exact Module.Finite.of_restrictScalars_finite ℚ_[p] K L

end Inclusion

section Galois

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (L : IntermediateField K (PadicAlgCl p))
  [Normal K L]

theorem restrictNormalHom_surjective :
    Function.Surjective (AlgEquiv.restrictNormalHom L : Gal(PadicAlgCl p/K) →* Gal(L/K)) :=
  AlgEquiv.restrictNormalHom_surjective _

theorem ker_restrictNormalHom :
    (AlgEquiv.restrictNormalHom L : Gal(PadicAlgCl p/K) →* Gal(L/K)).ker = L.fixingSubgroup :=
  L.restrictNormalHom_ker

instance fixingSubgroup_normal : L.fixingSubgroup.Normal := by
  rw [← ker_restrictNormalHom K L]
  exact MonoidHom.normal_ker _

def galQuotientEquiv : Gal(PadicAlgCl p/K) ⧸ L.fixingSubgroup ≃* Gal(L/K) :=
  QuotientGroup.liftEquiv _ (restrictNormalHom_surjective K L) L.restrictNormalHom_ker.symm

end Galois

section Examples

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
  (L : IntermediateField K (PadicAlgCl p)) [FiniteDimensional K L]

example : IsNonarchimedeanLocalField K := inferInstance
example : ValuativeExtension ℚ_[p] K := inferInstance
example : IsNonarchimedeanLocalField L := inferInstance
example : ValuativeExtension K L := inferInstance
example : Algebra 𝒪[K] 𝒪[L] := inferInstance
example : Algebra.IsSeparable K L := inferInstance
example : Normal K (PadicAlgCl p) := inferInstance
example (i : ℤ) : Subgroup Gal(L/K) := GroundTheory.LocalField.lowerRamificationGroup K L i
example : ℕ := GroundTheory.LocalField.differentExponent K L
example : differentIdeal 𝒪[K] 𝒪[L] = 𝓂[L] ^ GroundTheory.LocalField.differentExponent K L :=
  GroundTheory.LocalField.differentIdeal_eq_maximalIdeal_pow K L
example [IsGalois K L] (v : ℝ) : Subgroup Gal(L/K) := GroundTheory.LocalField.upperRamificationGroup K L v
example {K' L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K' ≤ L') [FiniteDimensional ℚ_[p] K']
    [FiniteDimensional ℚ_[p] L'] : ℕ :=
  letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI := valuativeExtension_inclusion h
  haveI := finiteDimensional_inclusion h
  GroundTheory.LocalField.differentExponent K' L'

end Examples

end GroundTheory.PAdicHodge
