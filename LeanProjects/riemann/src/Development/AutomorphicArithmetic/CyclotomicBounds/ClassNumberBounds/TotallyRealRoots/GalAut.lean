import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalDefs

namespace KStar.TotallyRealRoots

theorem exists_aut_pow_roots (Ω : Type*) [Field Ω] [CharZero Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic ℚ Ω] {M : ℕ} [NeZero M] (a : (ZMod M)ˣ) :
    ∃ g : Ω ≃ₐ[ℚ] Ω, ∀ ζ : Ω, ζ ^ M = 1 → g ζ = ζ ^ (a : ZMod M).val := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  have hc : IsCyclotomicExtension {M} ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : NumberField (IntermediateField.adjoin ℚ {ζ}) := IsCyclotomicExtension.numberField {M} ℚ _
  let σ := (IsCyclotomicExtension.Rat.galEquivZMod M (IntermediateField.adjoin ℚ {ζ})).symm a
  refine ⟨σ.liftNormal Ω, fun η hη => ?_⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
  let z : IntermediateField.adjoin ℚ {ζ} := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  have hz : z ^ M = 1 := Subtype.ext (by simpa [z] using hζ.pow_eq_one)
  have h1 := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq M _ σ hz
  have h2 := AlgEquiv.liftNormal_commutes σ Ω z
  have h3 : σ.liftNormal Ω ζ = ζ ^ (a : ZMod M).val := by
    have : algebraMap _ Ω z = ζ := rfl
    rw [this, h1, map_pow, this] at h2
    rwa [MulEquiv.apply_symm_apply] at h2
  rw [map_pow, h3, ← pow_mul, ← pow_mul, mul_comm]

theorem aut_comp_embedding {Ω : Type*} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] {K : Type*} [Field K]
    [NumberField K] [IsCyclotomicExtension {N} ℚ K] (φ : K →+* Ω) (g : Ω →+* Ω) (a : (ZMod N)ˣ)
    (h : ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ ^ (a : ZMod N).val) (x : K) :
    g (φ x) = φ ((IsCyclotomicExtension.Rat.galEquivZMod N K).symm a x) := by
  set σ := (IsCyclotomicExtension.Rat.galEquivZMod N K).symm a with hσ
  have hσa : IsCyclotomicExtension.Rat.galEquivZMod N K σ = a :=
    (IsCyclotomicExtension.Rat.galEquivZMod N K).apply_symm_apply a
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have key : (g.comp φ).toRatAlgHom = (φ.comp (σ : K →+* K)).toRatAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show g (φ _) = φ (σ _)
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N K σ hζ.pow_eq_one, hσa, map_pow,
      h _ (by rw [← map_pow, hζ.pow_eq_one, map_one])]
  exact congrArg (fun f : K →ₐ[ℚ] Ω => f x) key

theorem exists_class_of_aut {Ω : Type*} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] {N : ℕ} [NeZero N]
    (g : Ω ≃+* Ω) : ∃ a : (ZMod N)ˣ, ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ ^ (a : ZMod N).val := by
  have hn : Nat.card (rootsOfUnity N Ω) = N := HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω N
  refine ⟨modularCyclotomicCharacter Ω hn g, fun ζ hζ => ?_⟩
  have := modularCyclotomicCharacter.spec Ω hn g (t := (rootsOfUnity.mkOfPowEq ζ hζ : Ωˣ)) (rootsOfUnity.mkOfPowEq ζ hζ).2
  simpa using this

end KStar.TotallyRealRoots
