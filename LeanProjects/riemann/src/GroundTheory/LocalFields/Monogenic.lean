import Mathlib
import GroundTheory.LocalFields.Eisenstein

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial IsDiscreteValuationRing IsLocalRing

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem residue_aeval_integer (p : 𝒪[K][X]) (x : 𝒪[L]) :
    residue 𝒪[L] (aeval x p) = aeval (residue 𝒪[L] x) (p.map (residue 𝒪[K])) := by
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
  congr 1

variable (K) in

theorem adjoin_eq_top_of_residue_of_addVal_eq_one {x : 𝒪[L]}
    (hx : Algebra.adjoin 𝓀[K] {residue 𝒪[L] x} = ⊤) {π : 𝒪[L]}
    (hπA : π ∈ Algebra.adjoin 𝒪[K] {x}) (hπ : addVal 𝒪[L] π = 1) :
    Algebra.adjoin 𝒪[K] {x} = ⊤ := by
  set A := Algebra.adjoin 𝒪[K] {x}
  set e := ramificationIndex K L

  have hres : ∀ w : 𝒪[L], ∃ a ∈ A, ∃ w', w = a + π * w' := by
    intro w
    have hw : residue 𝒪[L] w ∈ Algebra.adjoin 𝓀[K] {residue 𝒪[L] x} := by
      rw [hx]; trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hw
    obtain ⟨p, hp⟩ := hw
    obtain ⟨p₀, rfl⟩ := Polynomial.map_surjective (residue 𝒪[K]) residue_surjective p
    refine ⟨aeval x p₀, ?_, ?_⟩
    · exact aeval_mem_adjoin_singleton 𝒪[K] x
    have hm : w - aeval x p₀ ∈ IsLocalRing.maximalIdeal 𝒪[L] := by
      rw [← residue_eq_zero_iff, map_sub, residue_aeval_integer]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hp
      rw [hp, sub_self]
    rw [← pow_one (IsLocalRing.maximalIdeal 𝒪[L]), mem_maximalIdeal_pow_iff_le_addVal, Nat.cast_one, ← hπ,
      addVal_le_iff_dvd] at hm
    obtain ⟨w', hw'⟩ := hm
    exact ⟨w', by rw [← hw']; ring⟩
  have step : ∀ k : ℕ, ∀ z : 𝒪[L], ∃ a ∈ A, ∃ w, z = a + π ^ k * w := by
    intro k
    induction k with
    | zero => exact fun z => ⟨0, zero_mem _, z, by simp⟩
    | succ k ih =>
      intro z
      obtain ⟨a, ha, w, rfl⟩ := ih z
      obtain ⟨b, hb, w', rfl⟩ := hres w
      refine ⟨a + π ^ k * b, add_mem ha (mul_mem (pow_mem hπA k) hb), w', ?_⟩
      ring
  obtain ⟨ϖK, hϖK⟩ := exists_irreducible 𝒪[K]
  have hassoc : Associated (algebraMap 𝒪[K] 𝒪[L] ϖK) (π ^ e) := by
    rw [← addVal_eq_iff_associated, addVal_algebraMap_integer, addVal_uniformizer hϖK,
      addVal_pow, hπ, mul_one, nsmul_eq_mul, mul_one]
  obtain ⟨u, hu⟩ := hassoc
  have hle : (⊤ : Submodule 𝒪[K] 𝒪[L]) ≤
      Subalgebra.toSubmodule A ⊔ IsLocalRing.maximalIdeal 𝒪[K] • ⊤ := by
    intro z _
    obtain ⟨a, ha, w, rfl⟩ := step e z
    refine Submodule.add_mem_sup ha ?_
    rw [← hu, mul_assoc, ← Algebra.smul_def]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [hϖK.maximalIdeal_eq]
    exact Ideal.subset_span rfl
  have hnak := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle
  rw [eq_top_iff]
  intro z _
  exact hnak Submodule.mem_top

variable (K L) in

theorem exists_integer_adjoin_eq_top : ∃ x : 𝒪[L], Algebra.adjoin 𝒪[K] {x} = ⊤ := by
  classical
  obtain ⟨ξ, hξ⟩ := Field.exists_primitive_element_of_finite_top 𝓀[K] 𝓀[L]
  have hadj : Algebra.adjoin 𝓀[K] {ξ} = ⊤ := IntermediateField.adjoin_eq_top_iff.mp hξ
  have hint : IsIntegral 𝓀[K] ξ := Algebra.IsIntegral.isIntegral ξ
  set P := minpoly 𝓀[K] ξ
  have hsep : P.Separable := PerfectField.separable_of_irreducible (minpoly.irreducible hint)
  obtain ⟨P₀, hP₀⟩ := Polynomial.map_surjective (residue 𝒪[K]) residue_surjective P
  obtain ⟨x₀, hx₀⟩ := residue_surjective ξ

  have hy₀ : aeval x₀ P₀ ∈ IsLocalRing.maximalIdeal 𝒪[L] := by
    rw [← residue_eq_zero_iff, residue_aeval_integer, hP₀, hx₀]
    exact minpoly.aeval _ _
  have hd₀ : IsUnit (aeval x₀ (derivative P₀)) := by
    rw [← not_not (a := IsUnit _), ← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff,
      residue_aeval_integer, ← derivative_map, hP₀, hx₀]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)

  obtain ⟨x, hxres, hxval⟩ : ∃ x : 𝒪[L], residue 𝒪[L] x = ξ ∧ addVal 𝒪[L] (aeval x P₀) = 1 := by
    by_cases hsq : aeval x₀ P₀ ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2
    · obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[L]
      have hϖ1 : addVal 𝒪[L] ϖ = 1 := addVal_uniformizer hϖ
      refine ⟨x₀ + ϖ, ?_, ?_⟩
      · rw [map_add, hx₀, (residue_eq_zero_iff ϖ).mpr hϖ.not_isUnit, add_zero]
      obtain ⟨k, hk⟩ := binomExpansion (P₀.map (algebraMap 𝒪[K] 𝒪[L])) x₀ ϖ
      rw [eval_map_algebraMap, eval_map_algebraMap, derivative_map, eval_map_algebraMap] at hk
      have hϖm : ϖ ∈ IsLocalRing.maximalIdeal 𝒪[L] := hϖ.not_isUnit
      have hϖsq : ϖ ^ 2 ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2 := Ideal.pow_mem_pow hϖm 2
      refine addVal_eq_one_of_mem_of_notMem_sq ?_ ?_
      · rw [hk]
        refine add_mem (add_mem hy₀ (Ideal.mul_mem_left _ _ hϖm)) ?_
        exact Ideal.mul_mem_left _ _ (Ideal.pow_le_self two_ne_zero hϖsq)
      · intro hmem
        have h1 : aeval x₀ (derivative P₀) * ϖ ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2 := by
          have : aeval x₀ (derivative P₀) * ϖ =
              aeval (x₀ + ϖ) P₀ - aeval x₀ P₀ - k * ϖ ^ 2 := by rw [hk]; ring
          rw [this]
          exact sub_mem (sub_mem hmem hsq) (Ideal.mul_mem_left _ _ hϖsq)
        obtain ⟨v, hv⟩ := hd₀
        have h2 : ϖ ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2 := by
          have := Ideal.mul_mem_left (IsLocalRing.maximalIdeal 𝒪[L] ^ 2) (↑v⁻¹ : 𝒪[L]) h1
          rwa [← hv, ← mul_assoc, Units.inv_mul, one_mul] at this
        rw [mem_maximalIdeal_pow_iff_le_addVal, hϖ1] at h2
        norm_num at h2
    · exact ⟨x₀, hx₀, addVal_eq_one_of_mem_of_notMem_sq hy₀ hsq⟩
  refine ⟨x, adjoin_eq_top_of_residue_of_addVal_eq_one K (π := aeval x P₀) ?_ ?_ hxval⟩
  · rw [hxres]; exact hadj
  · exact aeval_mem_adjoin_singleton 𝒪[K] x

end GroundTheory.LocalField
