import Mathlib

private theorem UpperTheory.algebraic_over_finite_field_integral (k L : Type) [Field k] [Finite k] [Field L] [Algebra k L]
    (y : L) (h : IsAlgebraic k y) : IsIntegral ℤ y := by
  have hi : IsIntegral k y := h.isIntegral
  haveI : FiniteDimensional k (IntermediateField.adjoin k {y}) := IntermediateField.adjoin.finiteDimensional hi
  haveI : Finite (IntermediateField.adjoin k {y}) := Module.finite_of_finite k
  let g : ℕ → IntermediateField.adjoin k {y} := fun n =>
    ⟨y ^ (n + 1), pow_mem (IntermediateField.mem_adjoin_simple_self k y) _⟩
  obtain ⟨m, n, hmn, hg⟩ := Finite.exists_ne_map_eq_of_infinite g
  have hpow : y ^ (m + 1) = y ^ (n + 1) := congrArg Subtype.val hg
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · refine ⟨Polynomial.X ^ (n + 1) - Polynomial.X ^ (m + 1), Polynomial.monic_X_pow_sub ?_, ?_⟩
    · rw [Polynomial.degree_X_pow]
      exact_mod_cast Nat.succ_lt_succ hlt
    · simp [hpow]
  · refine ⟨Polynomial.X ^ (m + 1) - Polynomial.X ^ (n + 1), Polynomial.monic_X_pow_sub ?_, ?_⟩
    · rw [Polynomial.degree_X_pow]
      exact_mod_cast Nat.succ_lt_succ hlt
    · simp [hpow]

open Polynomial in
theorem UpperTheory.residue_isIntegral_of_algebraic_over_dvr :
    ∀ (A K : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] [Field K] (V : ValuationSubring K) (f : A →+* V), Function.Injective f → IsLocalHom f → ∀ x : V, (∃ p : Polynomial A, p ≠ 0 ∧ p.eval₂ (V.subtype.comp f) x = 0) → IsIntegral ℤ (IsLocalRing.residue V x) := by
  intro A K _ _ _ _ _ V f hf _ x hx
  classical
  obtain ⟨p, hp0, hpx⟩ := hx
  letI : NormalizationMonoid A := UniqueFactorizationMonoid.normalizationMonoid.toNormalizationMonoid
  letI : NormalizedGCDMonoid A := UniqueFactorizationMonoid.toNormalizedGCDMonoid A
  have hV : Polynomial.eval₂ f x p = 0 := by
    apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero]
    exact (Polynomial.hom_eval₂ p f V.subtype x).trans hpx
  set q := p.primPart with hq
  have hcont : f p.content ≠ 0 := by
    intro h0
    apply hp0
    rw [← Polynomial.content_eq_zero_iff]
    exact hf (h0.trans (map_zero f).symm)
  have hqx : Polynomial.eval₂ f x q = 0 := by
    have e := Polynomial.eq_C_content_mul_primPart p
    rw [e, Polynomial.eval₂_mul, Polynomial.eval₂_C] at hV
    exact (mul_eq_zero.1 hV).resolve_left hcont
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hqbar : q.map (IsLocalRing.residue A) ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C π ∣ q := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have hi : IsLocalRing.residue A (q.coeff i) = 0 := by
        rw [← Polynomial.coeff_map, h0, Polynomial.coeff_zero]
      rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hi
      exact hi
    exact hπ.not_isUnit (Polynomial.isPrimitive_primPart p π hdvd)
  letI : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V) :=
    (IsLocalRing.ResidueField.map f).toAlgebra
  have halg : IsAlgebraic (IsLocalRing.ResidueField A) (IsLocalRing.residue V x) := by
    refine ⟨q.map (IsLocalRing.residue A), hqbar, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have e : (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V)).comp (IsLocalRing.residue A) =
        (IsLocalRing.residue V).comp f := by
      ext a
      exact IsLocalRing.ResidueField.map_residue f a
    rw [e, ← Polynomial.hom_eval₂, hqx, map_zero]
  exact UpperTheory.algebraic_over_finite_field_integral (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V) _ halg
