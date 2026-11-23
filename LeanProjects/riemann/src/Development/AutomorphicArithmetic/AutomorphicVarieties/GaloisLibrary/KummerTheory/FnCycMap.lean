import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem rootSet_X_pow_sub_one_eq_setOf_exists_mem_singleton (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (k : ℕ) (hk : k ≠ 0) :
    (Polynomial.X ^ k - 1 : Polynomial F).rootSet Ω = {b : Ω | ∃ m ∈ ({k} : Set ℕ), m ≠ 0 ∧ b ^ m = 1} := by
  have hp : (Polynomial.X ^ k - 1 : Polynomial F) ≠ 0 := by
    simpa using Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hk) (1 : F)
  ext b
  rw [Polynomial.mem_rootSet_of_ne hp]
  simp [sub_eq_zero, hk]

private theorem apply_mem_fn_of_isLift (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (l n : ℕ) (τ : F ≃+* F)
    (σ : Ω ≃+* Ω) (h : IsLift τ σ) (x : Ω) (hx : x ∈ Fn F Ω l n) : σ x ∈ Fn F Ω l n := by
  have hx' : x ∈ IntermediateField.adjoin F ((Polynomial.X ^ l ^ n - 1 : Polynomial F).rootSet Ω) := hx
  show σ x ∈ IntermediateField.adjoin F ((Polynomial.X ^ l ^ n - 1 : Polynomial F).rootSet Ω)
  refine IntermediateField.adjoin_induction F
    (p := fun x _ => σ x ∈ IntermediateField.adjoin F ((Polynomial.X ^ l ^ n - 1 : Polynomial F).rootSet Ω))
    ?_ ?_ ?_ ?_ ?_ hx'
  · intro y hy
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet] at hy ⊢
    obtain ⟨hp, hy⟩ := hy
    refine ⟨hp, ?_⟩
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one] at hy ⊢
    rw [← map_pow, ← map_one σ, ← map_sub, hy, map_zero]
  · intro c
    rw [h c]
    exact IntermediateField.algebraMap_mem _ _
  · intro y z _ _ hy hz
    rw [map_add]
    exact add_mem hy hz
  · intro y _ hy
    rw [map_inv₀]
    exact inv_mem hy
  · intro y z _ _ hy hz
    rw [map_mul]
    exact mul_mem hy hz

theorem UpperTheory.V.Kum.fnCyc :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), IsCyclotomicExtension {l ^ n} F (Fn F Ω l n) ∧ (∀ (τ : F ≃+* F) (σ : Ω ≃+* Ω), IsLift τ σ → ∃ τ' : Fn F Ω l n ≃+* Fn F Ω l n, IsLift τ' σ) ∧ (2 ≤ n → IsTotallyComplex (Fn F Ω l n)) := by
  intro F Ω _ _ _ _ _ l _ n
  have hl : l.Prime := Fact.out
  have hk : l ^ n ≠ 0 := pow_ne_zero _ hl.ne_zero
  haveI : NeZero (l ^ n) := ⟨hk⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hFn : Fn F Ω l n = IntermediateField.adjoin F {b : Ω | ∃ m ∈ ({l ^ n} : Set ℕ), m ≠ 0 ∧ b ^ m = 1} := by
    show IntermediateField.adjoin F _ = _
    rw [rootSet_X_pow_sub_one_eq_setOf_exists_mem_singleton F Ω _ hk]
  refine ⟨?_, ?_, ?_⟩
  · rw [hFn]
    refine IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot (S := {l ^ n}) (K := F) (L := Ω) ?_
    intro m hm _
    rw [Set.mem_singleton_iff] at hm
    subst hm
    exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  · intro τ σ h
    have hs : IsLift τ.symm σ.symm := by
      intro x
      apply σ.injective
      rw [RingEquiv.apply_symm_apply, h, RingEquiv.apply_symm_apply]
    refine ⟨{ toFun := fun x => ⟨σ x, apply_mem_fn_of_isLift F Ω l n τ σ h x.1 x.2⟩,
              invFun := fun x => ⟨σ.symm x, apply_mem_fn_of_isLift F Ω l n τ.symm σ.symm hs x.1 x.2⟩,
              left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.1),
              right_inv := fun x => Subtype.ext (σ.apply_symm_apply x.1),
              map_mul' := fun x y => Subtype.ext (map_mul σ x.1 y.1),
              map_add' := fun x y => Subtype.ext (map_add σ x.1 y.1) }, ?_⟩
    intro x
    rfl
  · intro hn2
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
    have hzmem : z ∈ Fn F Ω l n := by
      rw [hFn]
      exact IntermediateField.subset_adjoin _ _ ⟨l ^ n, rfl, hk, hz.pow_eq_one⟩
    have hζ : IsPrimitiveRoot (⟨z, hzmem⟩ : Fn F Ω l n) (l ^ n) :=
      IsPrimitiveRoot.of_map_of_injective (f := (Fn F Ω l n).val) hz Subtype.val_injective
    have hcyc := IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (K := ℚ) hζ
    have h2 : 2 < l ^ n := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ l ^ 2 := Nat.pow_le_pow_left hl.two_le 2
        _ ≤ l ^ n := Nat.pow_le_pow_right hl.pos hn2
    have htc := @IsCyclotomicExtension.Rat.isTotallyComplex (l ^ n) _
      (IntermediateField.adjoin ℚ {(⟨z, hzmem⟩ : Fn F Ω l n)}) _ _ hcyc h2
    exact isTotallyComplex_of_algebra (IntermediateField.adjoin ℚ {(⟨z, hzmem⟩ : Fn F Ω l n)}) (Fn F Ω l n)
