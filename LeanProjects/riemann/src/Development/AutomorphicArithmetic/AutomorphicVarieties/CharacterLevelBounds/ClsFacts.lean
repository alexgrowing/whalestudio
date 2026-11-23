import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem exists_primitiveRoot_of_isAlgClosure' (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : ℕ) [NeZero N] : ∃ ζ : Ω, IsPrimitiveRoot ζ N := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω N

private theorem cls_apply_root_of_unity_eq_pow (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : ℕ) [NeZero N] (σ : G k Ω) (ζ : Ω) (hζ : ζ ^ N = 1) :
    σ ζ = ζ ^ ((cls k Ω N σ : (ZMod N)ˣ) : ZMod N).val := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp [NeZero.ne N] at hζ
  have ht : Units.mk0 ζ h0 ∈ rootsOfUnity N Ω := by
    rw [mem_rootsOfUnity]
    ext
    simpa using hζ
  obtain ⟨ξ, hξ⟩ := exists_primitiveRoot_of_isAlgClosure' k Ω N
  have := modularCyclotomicCharacter.spec Ω hξ.card_rootsOfUnity
    (MulSemiringAction.toRingAut (G k Ω) Ω σ) ht
  exact this

private theorem cls_eq_of_forall_root_of_unity_apply_eq_pow (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : ℕ) [NeZero N] (σ : G k Ω) (u : (ZMod N)ˣ)
    (h : ∀ ζ : Ω, ζ ^ N = 1 → σ ζ = ζ ^ (u : ZMod N).val) : cls k Ω N σ = u := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isAlgClosure' k Ω N
  ext1
  refine (modularCyclotomicCharacter.unique Ω hζ.card_rootsOfUnity
    (MulSemiringAction.toRingAut (G k Ω) Ω σ) (c := (u : ZMod N)) ?_).symm
  intro t ht
  rw [mem_rootsOfUnity] at ht
  have ht' : (t : Ω) ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  exact h t ht'

private theorem root_of_unity_pow_natCast_zmod_val {Ω : Type} [Field Ω] (N : ℕ) [NeZero N] (ζ : Ω) (hζ : ζ ^ N = 1)
    (b : ℕ) : ζ ^ ((b : ZMod N)).val = ζ ^ b := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div b N, pow_add, pow_mul, hζ, one_pow, mul_one]

private theorem cls_eq_one_of_fixes_primitiveRoot (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : ℕ) [NeZero N] (σ : G k Ω) (ζ : Ω) (hζ : IsPrimitiveRoot ζ N)
    (hσ : σ ζ = ζ) : cls k Ω N σ = 1 := by
  apply cls_eq_of_forall_root_of_unity_apply_eq_pow
  intro ξ hξ
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
  have h1 := root_of_unity_pow_natCast_zmod_val N _ hξ 1
  rw [Nat.cast_one, pow_one] at h1
  rw [map_pow, hσ, Units.val_one, h1]

theorem UpperTheory.V.Chr.clsFacts :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (N : ℕ) [NeZero N],
          IsOpen ((cls k Ω N).ker : Set (G k Ω)) ∧ (∀ (M : ℕ) [NeZero M] (h : M ∣ N), (ZMod.unitsMap h).comp (cls k Ω N) = cls k Ω M) ∧
          (∀ (σ : G k Ω) (u : (ZMod N)ˣ), (∀ ζ : Ω, ζ ^ N = 1 → σ ζ = ζ ^ (u : ZMod N).val) → cls k Ω N σ = u) ∧
          (∀ σ : G k Ω, IsConjOm σ.toRingEquiv → cls k Ω N σ = -1) ∧
          ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → Ine (F := k) A ≤ (cls k Ω N).ker := by
  intro k Ω _ _ _ _ _ N _
  refine ⟨?_, ?_, fun σ u h => cls_eq_of_forall_root_of_unity_apply_eq_pow k Ω N σ u h, ?_, ?_⟩
  · obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isAlgClosure' k Ω N
    haveI : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
    have hi : IsIntegral k ζ := (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
    haveI : FiniteDimensional k (IntermediateField.adjoin k {ζ}) :=
      IntermediateField.adjoin.finiteDimensional hi
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin k {ζ}))
    intro σ hσ
    rw [MonoidHom.mem_ker]
    exact cls_eq_one_of_fixes_primitiveRoot k Ω N σ ζ hζ ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ ζ
      (IntermediateField.mem_adjoin_simple_self k ζ))
  · intro M _ hMN
    ext1 σ
    symm
    apply cls_eq_of_forall_root_of_unity_apply_eq_pow
    intro ζ hζ
    rw [MonoidHom.comp_apply, ZMod.unitsMap_val, ZMod.cast_eq_val, root_of_unity_pow_natCast_zmod_val M ζ hζ]
    obtain ⟨d, hd⟩ := hMN
    exact cls_apply_root_of_unity_eq_pow k Ω N σ ζ (by rw [hd, pow_mul, hζ, one_pow])
  · intro σ hσ
    obtain ⟨j, hj⟩ := hσ
    apply cls_eq_of_forall_root_of_unity_apply_eq_pow
    intro ζ hζ
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
    have h0 : ζ ≠ 0 := by
      rintro rfl
      simp [NeZero.ne N] at hζ
    have hval : ((-1 : (ZMod N)ˣ) : ZMod N) = ((N - 1 : ℕ) : ZMod N) := by
      rw [Units.val_neg, Units.val_one, Nat.cast_sub hN1, ZMod.natCast_self, Nat.cast_one, zero_sub]
    rw [hval, root_of_unity_pow_natCast_zmod_val N ζ hζ, pow_sub₀ ζ h0 hN1, hζ, pow_one, one_mul]
    apply j.injective
    have hjζ := hj ζ
    simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv] at hjζ
    rw [hjζ, map_inv₀]
    have hz : (j ζ) ^ N = 1 := by rw [← map_pow, hζ, map_one]
    have hn : ‖j ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz (NeZero.ne N)
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
    simp
  · intro A hA σ hσ
    rw [MonoidHom.mem_ker]
    obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isAlgClosure' k Ω N
    apply cls_eq_one_of_fixes_primitiveRoot k Ω N σ ζ hζ
    have hin : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1 := hσ.2
    by_contra hne
    have h0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
    set ξ := σ ζ * ζ⁻¹ with hξdef
    have hξN : ξ ^ N = 1 := by
      rw [hξdef, mul_pow, inv_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul, inv_one]
    have hξ1 : ξ ≠ 1 := by
      intro h
      apply hne
      rw [hξdef, mul_inv_eq_one₀ h0] at h
      exact h
    have hv1 : ∀ x : Ω, x ^ N = 1 → A.valuation x = 1 := by
      intro x hx
      have hp : A.valuation x ^ N = 1 := by rw [← map_pow, hx, map_one]
      exact (pow_eq_one_iff.1 hp).resolve_right (NeZero.ne N)
    have hsum : ∑ i ∈ Finset.range N, ξ ^ i = 0 := by
      have hg := geom_sum_mul ξ N
      rw [hξN, sub_self] at hg
      exact (mul_eq_zero.1 hg).resolve_right (sub_ne_zero.2 hξ1)
    have hNeq : (N : Ω) = (1 - ξ) * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range i, ξ ^ j := by
      rw [Finset.mul_sum]
      simp_rw [mul_neg_geom_sum]
      rw [Finset.sum_sub_distrib, hsum]
      simp
    have hξA : ξ ∈ A := (A.valuation_le_one_iff ξ).1 (hv1 ξ hξN).le
    have hSA : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range i, ξ ^ j) ∈ A :=
      sum_mem fun i _ => sum_mem fun j _ => pow_mem hξA j
    have hS : A.valuation (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range i, ξ ^ j) ≤ 1 :=
      (A.valuation_le_one_iff _).2 hSA
    have hdiff : σ ζ - ζ = -(ζ * (1 - ξ)) := by
      rw [hξdef]
      field_simp
      ring
    have hlt : A.valuation (1 - ξ) < 1 := by
      have := hin ζ (hv1 ζ hζ.pow_eq_one).le
      rw [hdiff, Valuation.map_neg, map_mul, hv1 ζ hζ.pow_eq_one, one_mul] at this
      exact this
    apply hA
    rw [hNeq, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hS) hlt
