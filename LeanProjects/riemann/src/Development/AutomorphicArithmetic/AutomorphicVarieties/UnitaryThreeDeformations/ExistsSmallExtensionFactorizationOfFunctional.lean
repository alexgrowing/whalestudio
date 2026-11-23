import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem isCO_of_surj {O : Type} [CommRing O] [IsLocalRing O] {R S : Type} [CommRing R] [Algebra O R]
    [IsCO O R] [Finite R] [CommRing S] [Algebra O S] [Nontrivial S] (f : R →ₐ[O] S)
    (hf : Function.Surjective f) :
    ∃ _ : IsCO O S, ∀ x : R, f x ∈ maximalIdeal S ↔ x ∈ maximalIdeal R := by
  haveI : IsLocalRing S := IsLocalRing.of_surjective' (f : R →+* S) hf
  haveI : Finite S := Finite.of_surjective f hf
  haveI hl : IsLocalHom (f : R →+* S) := IsLocalHom.of_surjective (f : R →+* S) hf
  have hm : ∀ x : R, f x ∈ maximalIdeal S ↔ x ∈ maximalIdeal R := fun x =>
    ⟨fun h hu => h (hu.map f), fun h hu => h (hl.map_nonunit x hu)⟩
  haveI : IsArtinianRing S := inferInstance
  refine ⟨{ complete := inferInstance, isLocalHom := ⟨fun a ha => ?_⟩, res_surj := fun y => ?_ }, hm⟩
  · rw [← f.commutes] at ha
    exact IsLocalHom.map_nonunit (f := algebraMap O R) a (hl.map_nonunit _ ha)
  · obtain ⟨x, rfl⟩ := hf y
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    refine ⟨a, ?_⟩
    rw [← f.commutes, ← map_sub]
    exact (hm _).2 ha

theorem UpperTheory.exists_small_extension_factorization_of_functional :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [CommRing R'] [Algebra O R'] (p : R →ₐ[O] R'), maximalIdeal R * RingHom.ker p = ⊥ → RingHom.ker p ≤ maximalIdeal R → ∀ φ : RingHom.ker p →ₗ[O] ResidueField O, φ ≠ 0 →
     ∃ (R'' : Type) (_ : CommRing R'') (_ : Algebra O R'') (_ : IsCO O R'') (p₁ : R →ₐ[O] R'') (q : R'' →ₐ[O] R') (ε : ResidueField O →ₗ[O] R''), Function.Surjective p₁ ∧ q.comp p₁ = p ∧ ¬ Function.Injective q ∧ (∀ x : RingHom.ker p, p₁ x = ε (φ x)) ∧ (∀ y, q (ε y) = 0) ∧ (∀ y, ε y ∈ maximalIdeal R'') ∧ ∀ x ∈ maximalIdeal R'', ∀ y, x * ε y = 0 := by
  intro O _ _ R R' _ _ _ _ _ _ p hmul hle φ hφ
  have hz : ∀ m ∈ maximalIdeal R, ∀ x ∈ RingHom.ker p, m * x = 0 := fun m hm x hx => by
    have := Ideal.mul_mem_mul hm hx
    rwa [hmul, Ideal.mem_bot] at this
  let J : Ideal R :=
    { carrier := {x | ∃ h : x ∈ RingHom.ker p, φ ⟨x, h⟩ = 0}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, ?_⟩
        have : (⟨a + b, add_mem ha hb⟩ : RingHom.ker p) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        rw [this, map_add, ha', hb', add_zero]
      zero_mem' := ⟨zero_mem _, map_zero φ⟩
      smul_mem' := by
        rintro r x ⟨hx, hx'⟩
        refine ⟨Ideal.mul_mem_left _ r hx, ?_⟩
        obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) r
        have : (⟨r • x, Ideal.mul_mem_left _ r hx⟩ : RingHom.ker p) = a • ⟨x, hx⟩ := by
          apply Subtype.ext
          have h := hz _ ha x hx
          rw [sub_mul, sub_eq_zero] at h
          show r * x = a • x
          rw [h, Algebra.smul_def]
        rw [this, map_smul, hx', smul_zero] }
  have hJ : ∀ x : RingHom.ker p, (x : R) ∈ J ↔ φ x = 0 := fun x =>
    ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩
  have hJp : ∀ x ∈ J, p x = 0 := fun x ⟨h, _⟩ => h
  obtain ⟨x0, hx0⟩ : ∃ x, φ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (LinearMap.ext h)
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨a, ha⟩ := residue_surjective (y * (φ x0)⁻¹)
    refine ⟨a • x0, ?_⟩
    rw [map_smul, Algebra.smul_def, ResidueField.algebraMap_eq, ha, inv_mul_cancel_right₀ hx0]
  have hJtop : J ≠ ⊤ := fun h => hx0 ((hJ x0).1 (h ▸ Submodule.mem_top))
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJtop
  have hp1 : Function.Surjective (Ideal.Quotient.mkₐ O J) := Ideal.Quotient.mkₐ_surjective O J
  obtain ⟨inst, hm⟩ := isCO_of_surj (Ideal.Quotient.mkₐ O J) hp1
  let ψ : RingHom.ker p →ₗ[O] R ⧸ J :=
    (Ideal.Quotient.mkₐ O J).toLinearMap ∘ₗ ((RingHom.ker p).subtype.restrictScalars O)
  have hψ : ∀ x : RingHom.ker p, ψ x = Ideal.Quotient.mkₐ O J x := fun _ => rfl
  have hker : LinearMap.ker φ ≤ LinearMap.ker ψ := fun x hx =>
    Ideal.Quotient.eq_zero_iff_mem.2 ((hJ x).2 hx)
  let ε : ResidueField O →ₗ[O] R ⧸ J :=
    (LinearMap.ker φ).liftQ ψ hker ∘ₗ (φ.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hε : ∀ x : RingHom.ker p, ε (φ x) = Ideal.Quotient.mkₐ O J x := fun x => by
    have : (φ.quotKerEquivOfSurjective hsurj).symm (φ x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker φ).liftQ ψ hker ((φ.quotKerEquivOfSurjective hsurj).symm (φ x)) = _
    rw [this, Submodule.liftQ_apply, hψ]
  have hq : ∀ x : R, Ideal.Quotient.liftₐ J p hJp (Ideal.Quotient.mkₐ O J x) = p x := fun _ => rfl
  refine ⟨R ⧸ J, inferInstance, inferInstance, inst, Ideal.Quotient.mkₐ O J, Ideal.Quotient.liftₐ J p hJp, ε,
    hp1, AlgHom.ext hq, fun hinj => ?_, fun x => (hε x).symm, fun y => ?_, fun y => ?_, fun x hx y => ?_⟩
  · have h : Ideal.Quotient.mkₐ O J (x0 : R) = 0 := hinj (by rw [hq, map_zero]; exact x0.2)
    exact hx0 ((hJ x0).1 (Ideal.Quotient.eq_zero_iff_mem.1 h))
  · obtain ⟨x, rfl⟩ := hsurj y
    rw [hε, hq]; exact x.2
  · obtain ⟨x, rfl⟩ := hsurj y
    rw [hε]; exact (hm _).2 (hle x.2)
  · obtain ⟨z, rfl⟩ := hsurj y
    obtain ⟨w, rfl⟩ := hp1 x
    rw [hε, ← map_mul, hz w ((hm w).1 hx) _ z.2, map_zero]
