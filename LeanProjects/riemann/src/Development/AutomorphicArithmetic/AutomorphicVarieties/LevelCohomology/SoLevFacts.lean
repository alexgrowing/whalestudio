import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCardLen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem finite_quot {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (b : O) (hb : b ≠ 0) : Finite (O ⧸ Ideal.span {b}) := by
  have hfl := isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hb)
  haveI : IsArtinianRing (O ⧸ Ideal.span {b}) :=
    isArtinian_of_tower O (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
  exact IsLocalRing.finite_quotient_iff.mpr
    (IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient _)

theorem UpperTheory.V.X.So.levFacts :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (a : O), a ≠ 0 → ∀ (M : Type) [AddCommGroup M] [Module O M], Nonempty (M ≃ₗ[O] (O ⧸ Ideal.span {a})) → Finite M ∧ (∃ r : ℕ, 0 < r ∧ ∀ m : M, (l ^ r) • m = 0) ∧ ∀ d : O, d ≠ 0 → Nat.card {m : M // d • m = 0} ≤ Nat.card (O ⧸ Ideal.span {d}) := by
  intro l _ O _ _ _ _ _ a ha M _ _ hne
  obtain ⟨e⟩ := hne
  haveI : CharZero O := charZero_of_injective_algebraMap (UpperTheory.V.Base.dvrFacts l O).1
  obtain ⟨-, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l O
  haveI := hfin
  haveI hQa : Finite (O ⧸ Ideal.span {a}) := finite_quot a ha
  haveI : Finite M := Finite.of_equiv _ e.symm.toEquiv
  have hkill : ∀ c : O, c ∈ Ideal.span {a} → ∀ z : O ⧸ Ideal.span {a}, c • z = 0 := by
    intro c hc z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hc
  have hgen : ∀ m : M, ∃ y : O, y • e.symm (Ideal.Quotient.mk _ 1) = m := by
    intro m
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e m)
    refine ⟨y, e.injective ?_⟩
    rw [map_smul, LinearEquiv.apply_symm_apply, ← hy, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul, mul_one]
  refine ⟨inferInstance, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := (IsLocalRing.finite_quotient_iff (R := O)).mp hQa
    refine ⟨n + 1, Nat.succ_pos n, fun m => ?_⟩
    have hmem : (l : O) ^ (n + 1) ∈ Ideal.span {a} :=
      hn (Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.pow_mem_pow hlm (n + 1)))
    apply e.injective
    rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
    exact hkill _ hmem _
  · intro d hd
    haveI : Finite (O ⧸ Ideal.span {d}) := finite_quot d hd
    let φ : M →ₗ[O] M := LinearMap.lsmul O M d
    have hker : Nat.card {m : M // d • m = 0} = Nat.card (LinearMap.ker φ) :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun m => by simp [φ]))
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker φ).toAddSubgroup
    have h2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.range φ).toAddSubgroup
    change Nat.card M = Nat.card (M ⧸ LinearMap.ker φ) * Nat.card (LinearMap.ker φ) at h1
    change Nat.card M = Nat.card (M ⧸ LinearMap.range φ) * Nat.card (LinearMap.range φ) at h2
    rw [Nat.card_congr φ.quotKerEquivRange.toEquiv] at h1
    have hpos : 0 < Nat.card (LinearMap.range φ) := Nat.card_pos
    have heq : Nat.card (LinearMap.ker φ) = Nat.card (M ⧸ LinearMap.range φ) := by
      have h3 := h1.symm.trans h2
      exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h3, mul_comm])
    rw [hker, heq]
    let x0 : M := e.symm (Ideal.Quotient.mk _ 1)
    let f : O →ₗ[O] M ⧸ LinearMap.range φ :=
      (LinearMap.range φ).mkQ ∘ₗ LinearMap.toSpanSingleton O M x0
    have hle : Ideal.span {d} ≤ LinearMap.ker f := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      simp only [SetLike.mem_coe, LinearMap.mem_ker, f, LinearMap.comp_apply,
        LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨x0, rfl⟩
    apply Nat.card_le_card_of_surjective ((Ideal.span {d}).liftQ f hle)
    intro z
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨y, rfl⟩ := hgen m
    exact ⟨Submodule.Quotient.mk y, rfl⟩
