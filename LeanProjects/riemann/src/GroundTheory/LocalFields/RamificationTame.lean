import Mathlib
import GroundTheory.LocalFields.Eisenstein
import GroundTheory.LocalFields.UnitsPowers
import GroundTheory.LocalFields.RamificationStructure
import GroundTheory.LocalFields.UnramifiedDefs
import GroundTheory.LocalFields.IntermediateField

noncomputable section

open scoped IntermediateField

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing IsDiscreteValuationRing

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem natCast_ramificationIndex_ne_zero
    (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    (ramificationIndex K L : 𝓀[L]) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff 𝓀[L] (ringChar 𝓀[L]), ← Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
  intro hdvd
  have h1 := Nat.Coprime.eq_one_of_dvd he.symm hdvd
  exact Nat.not_prime_one (h1 ▸ CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K]))

theorem exists_pow_eq_uniformizer_of_residueDegree_eq_one (hf : residueDegree K L = 1)
    (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    ∃ π : 𝒪[K], Irreducible π ∧ ∃ α : 𝒪[L], Irreducible α ∧
      α ^ ramificationIndex K L = algebraMap 𝒪[K] 𝒪[L] π ∧ K⟮(α : L)⟯ = ⊤ := by
  set e := ramificationIndex K L with he_def
  obtain ⟨ϖK, hϖK⟩ := exists_irreducible 𝒪[K]
  obtain ⟨ϖL, hϖL⟩ := exists_irreducible 𝒪[L]

  obtain ⟨u, hu⟩ : Associated (algebraMap 𝒪[K] 𝒪[L] ϖK) (ϖL ^ e) := by
    have h := map_maximalIdeal K L
    rw [hϖK.maximalIdeal_eq, hϖL.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
    exact h

  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_maximalIdeal K L hf (u : 𝒪[L])
  have hcu : IsUnit c := by
    by_contra hn
    have hnL : ¬ IsUnit (algebraMap 𝒪[K] 𝒪[L] c) := fun h ↦ hn (isUnit_of_map_unit _ _ h)
    have hmem : algebraMap 𝒪[K] 𝒪[L] c ∈ 𝓂[L] := (mem_maximalIdeal _).mpr hnL
    have : (u : 𝒪[L]) ∈ 𝓂[L] := by
      have := add_mem hc hmem
      rwa [sub_add_cancel] at this
    exact (mem_maximalIdeal _).mp this u.isUnit
  set c' := hcu.unit
  set cL : 𝒪[L]ˣ := Units.map (algebraMap 𝒪[K] 𝒪[L] : 𝒪[K] →* 𝒪[L]) c' with hcL
  have hcLval : (cL : 𝒪[L]) = algebraMap 𝒪[K] 𝒪[L] c := rfl

  have hv : u * cL⁻¹ ∈ unitFiltration L 1 := by
    rw [mem_unitFiltration, pow_one, Units.val_mul,
      show (u : 𝒪[L]) * ((cL⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) - 1 = ((u : 𝒪[L]) - cL) * ((cL⁻¹ : 𝒪[L]ˣ) : 𝒪[L])
        by rw [sub_mul, Units.mul_inv], hcLval]
    exact Ideal.mul_mem_right _ _ hc
  obtain ⟨w, hw⟩ := unitFiltration_one_le_range_pow (natCast_ramificationIndex_ne_zero K L he) hv
  have hw' : w ^ e = u * cL⁻¹ := hw
  have hinv : (w⁻¹) ^ e = cL * u⁻¹ := by rw [inv_pow, hw', mul_inv_rev, inv_inv]

  have htot : ramificationIndex K L = Module.finrank K L := by
    have := ramificationIndex_mul_residueDegree K L
    rwa [hf, mul_one] at this
  refine ⟨ϖK * (c' : 𝒪[K]), (irreducible_mul_isUnit c'.isUnit).mpr hϖK,
    ϖL * ((w⁻¹ : 𝒪[L]ˣ) : 𝒪[L]), (irreducible_mul_isUnit (w⁻¹).isUnit).mpr hϖL, ?_, ?_⟩
  · have hui := Units.mul_inv u
    calc (ϖL * ((w⁻¹ : 𝒪[L]ˣ) : 𝒪[L])) ^ e = ϖL ^ e * (((w⁻¹) ^ e : 𝒪[L]ˣ) : 𝒪[L]) := by
          rw [mul_pow, Units.val_pow_eq_pow_val]
      _ = algebraMap 𝒪[K] 𝒪[L] ϖK * u * (cL * ((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L])) := by
          rw [← hu, hinv, Units.val_mul]
      _ = algebraMap 𝒪[K] 𝒪[L] (ϖK * (c' : 𝒪[K])) := by
          rw [map_mul, show algebraMap 𝒪[K] 𝒪[L] (c' : 𝒪[K]) = cL from rfl]
          linear_combination (algebraMap 𝒪[K] 𝒪[L] ϖK * cL) * hui
  · exact adjoin_eq_top_of_irreducible htot ((irreducible_mul_isUnit (w⁻¹).isUnit).mpr hϖL)

variable {K L}

theorem exists_pow_eq_uniformizer_of_isUnramified (T : IntermediateField K L) [IsUnramified K T]
    (hf : residueDegree T L = 1) (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    ramificationIndex T L = ramificationIndex K L ∧
      ∃ π : 𝒪[T], Irreducible π ∧ ∃ α : 𝒪[L], Irreducible α ∧
        α ^ ramificationIndex K L = algebraMap 𝒪[T] 𝒪[L] π ∧ T⟮(α : L)⟯ = ⊤ := by
  have htow : ramificationIndex T L = ramificationIndex K L := by
    rw [ramificationIndex_tower K T L, IsUnramified.ramificationIndex_eq_one (K := K) (L := T), one_mul]
  have he' : Nat.Coprime (ramificationIndex T L) (ringChar 𝓀[T]) := by
    rw [htow, ← Algebra.ringChar_eq 𝓀[K] 𝓀[T]]
    exact he
  refine ⟨htow, ?_⟩
  rw [← htow]
  exact exists_pow_eq_uniformizer_of_residueDegree_eq_one T L hf he'

end GroundTheory.LocalField
