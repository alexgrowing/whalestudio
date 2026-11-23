import Mathlib

set_option autoImplicit false

noncomputable section

open Polynomial IsLocalRing

namespace Formalism.L2.Pj.AvAlg

variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

theorem mem_adjoin_mod (α : B) (hres : Algebra.adjoin (ResidueField A) {residue B α} = ⊤) (f : A[X])
    (hβ : Irreducible (aeval α f)) :
    ∀ (n : ℕ) (b : B), ∃ s ∈ Algebra.adjoin A {α}, ∃ c : B, b = s + aeval α f ^ n * c := by
  have hra : ∀ G : A[X], residue B (aeval α G) = aeval (residue B α) (G.map (residue A)) := by
    intro G
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
    congr 1
    all_goals (ext x; simp only [RingHom.comp_apply]; exact (IsLocalRing.ResidueField.algebraMap_residue x).symm)
  intro n
  induction n with
  | zero => intro b; exact ⟨0, Subalgebra.zero_mem _, b, by simp⟩
  | succ n ih =>
    intro b
    obtain ⟨s, hs, c, rfl⟩ := ih b
    have hc : residue B c ∈ Algebra.adjoin (ResidueField A) {residue B α} := by
      rw [hres]; exact Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hc
    obtain ⟨p, hp⟩ := hc
    obtain ⟨P, rfl⟩ := Polynomial.map_surjective (residue A) IsLocalRing.residue_surjective p
    have hm : c - aeval α P ∈ maximalIdeal B := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hra]
      rw [← hp]
      exact sub_self _
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hβ, Ideal.mem_span_singleton'] at hm
    obtain ⟨c', hc'⟩ := hm
    have hα : aeval α f ∈ Algebra.adjoin A {α} := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]; exact AlgHom.mem_range_self _ f
    have hP : aeval α P ∈ Algebra.adjoin A {α} := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]; exact AlgHom.mem_range_self _ P
    refine ⟨s + aeval α f ^ n * aeval α P, ?_, c', ?_⟩
    · exact Subalgebra.add_mem _ hs (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hα n) hP)
    · have e : c = aeval α P + c' * aeval α f := by rw [hc']; ring
      rw [e]
      ring

end Formalism.L2.Pj.AvAlg

namespace Formalism.L2.Pj.AvAlg

variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

theorem adjoin_eq_top_of_gen [Module.Finite A B] (hinj : Function.Injective (algebraMap A B)) (α : B)
    (hres : Algebra.adjoin (ResidueField A) {residue B α} = ⊤) (f : A[X]) (hβ : Irreducible (aeval α f)) :
    Algebra.adjoin A {α} = ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ0 : algebraMap A B ϖ ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; exact hϖ.ne_zero
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ0 hβ
  have hϖm : ϖ ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  have key : (⊤ : Submodule A B) ≤ Subalgebra.toSubmodule (Algebra.adjoin A {α}) ⊔ (maximalIdeal A) • ⊤ := by
    intro b _
    obtain ⟨s, hs, c, hc⟩ := mem_adjoin_mod α hres f hβ e b
    have e1 : b = s + ϖ • ((↑u⁻¹ : B) * c) := by
      rw [hc, Algebra.smul_def, hu]
      congr 1
      rw [mul_comm (↑u : B), mul_assoc, ← mul_assoc (↑u : B), Units.mul_inv, one_mul]
    rw [e1]
    exact Submodule.add_mem_sup ((Subalgebra.mem_toSubmodule _).mpr hs)
      (Submodule.smul_mem_smul hϖm Submodule.mem_top)
  have hfg : (⊤ : Submodule A B).FG := Module.Finite.fg_top
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot hfg
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge key
  rw [eq_top_iff]
  intro x _
  exact (Subalgebra.mem_toSubmodule _).mp (hle Submodule.mem_top)

end Formalism.L2.Pj.AvAlg

namespace Formalism.L2.Pj.AvAlg

variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

theorem residue_aeval (α : B) (G : A[X]) :
    residue B (aeval α G) = aeval (residue B α) (G.map (residue A)) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  congr 1
  all_goals (ext x; simp only [RingHom.comp_apply]; exact (IsLocalRing.ResidueField.algebraMap_residue x).symm)

theorem adjoin_residue_gen [Finite (ResidueField B)] :
    ∃ γ : ResidueField B, Algebra.adjoin (ResidueField A) {γ} = ⊤ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ResidueField B)ˣ)
  refine ⟨(g : ResidueField B), ?_⟩
  rw [eq_top_iff]
  intro x _
  by_cases hx : x = 0
  · rw [hx]; exact Subalgebra.zero_mem _
  · obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr (hg (Units.mk0 x hx)))
    have e : x = (g : ResidueField B) ^ n := by
      rw [← Units.val_pow_eq_pow_val, show g ^ n = Units.mk0 x hx from hn, Units.val_mk0]
    rw [e]
    exact Subalgebra.pow_mem (Algebra.adjoin (ResidueField A) {(g : ResidueField B)})
      (Algebra.subset_adjoin (Set.mem_singleton _)) n

theorem exists_adjoin_eq_top [Module.Finite A B] [Finite (ResidueField A)]
    (hinj : Function.Injective (algebraMap A B)) : ∃ α : B, Algebra.adjoin A {α} = ⊤ := by
  haveI : Finite (ResidueField B) := IsLocalRing.ResidueField.finite_of_finite (R := A) ‹_›
  obtain ⟨γ, hγ⟩ := adjoin_residue_gen (A := A) (B := B)
  obtain ⟨α0, rfl⟩ := IsLocalRing.residue_surjective γ
  have hint : IsIntegral (ResidueField A) (residue B α0) := IsIntegral.of_finite _ _
  have hsep : (minpoly (ResidueField A) (residue B α0)).Separable :=
    PerfectField.separable_of_irreducible (minpoly.irreducible hint)
  have hq0 : aeval (residue B α0) (minpoly (ResidueField A) (residue B α0)) = 0 := minpoly.aeval _ _
  have hq' : aeval (residue B α0) (derivative (minpoly (ResidueField A) (residue B α0))) ≠ 0 :=
    hsep.aeval_derivative_ne_zero hq0
  obtain ⟨P, hP⟩ := Polynomial.map_surjective (residue A) IsLocalRing.residue_surjective
    (minpoly (ResidueField A) (residue B α0))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hm : aeval α0 P ∈ maximalIdeal B := by
    rw [← IsLocalRing.residue_eq_zero_iff, residue_aeval, hP, hq0]
  have hd : IsUnit (aeval α0 (derivative P)) := by
    by_contra hnu
    have h3 : aeval α0 (derivative P) ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← IsLocalRing.residue_eq_zero_iff, residue_aeval, ← Polynomial.derivative_map, hP] at h3
    exact hq' h3
  by_cases h2 : aeval α0 P ∈ Ideal.span {π ^ 2}
  · refine ⟨α0 + π, adjoin_eq_top_of_gen hinj (α0 + π) ?_ P ?_⟩
    · have hr : residue B π = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).mpr (hmax ▸ Ideal.mem_span_singleton_self π)
      rw [map_add, hr, add_zero]; exact hγ
    · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp h2
      obtain ⟨k, hk⟩ := Polynomial.binomExpansion (P.map (algebraMap A B)) α0 π
      have e : aeval (α0 + π) P = π * (aeval α0 (derivative P) + π * (t + k)) := by
        simp only [Polynomial.aeval_def, ← Polynomial.eval_map] at ht ⊢
        rw [← Polynomial.derivative_map, hk, ← ht]
        ring
      have hv : IsUnit (aeval α0 (derivative P) + π * (t + k)) := by
        by_contra hnu
        have h1 : aeval α0 (derivative P) + π * (t + k) ∈ maximalIdeal B :=
          (IsLocalRing.mem_maximalIdeal _).mpr hnu
        have h3 : π * (t + k) ∈ maximalIdeal B := by
          rw [hmax]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self π)
        have h4 : aeval α0 (derivative P) ∈ maximalIdeal B := by
          simpa using Ideal.sub_mem _ h1 h3
        exact (IsLocalRing.mem_maximalIdeal _).mp h4 hd
      rw [e]
      exact (irreducible_mul_isUnit hv).mpr hπ
  · refine ⟨α0, adjoin_eq_top_of_gen hinj α0 hγ P ?_⟩
    rw [hmax] at hm
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hm
    have hwu : IsUnit w := by
      by_contra hnu
      apply h2
      have h5 : w ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rw [hmax, Ideal.mem_span_singleton'] at h5
      obtain ⟨v, hv⟩ := h5
      rw [Ideal.mem_span_singleton']
      exact ⟨v, by rw [← hw, ← hv]; ring⟩
    rw [← hw, mul_comm]
    exact (irreducible_mul_isUnit hwu).mpr hπ

end Formalism.L2.Pj.AvAlg
