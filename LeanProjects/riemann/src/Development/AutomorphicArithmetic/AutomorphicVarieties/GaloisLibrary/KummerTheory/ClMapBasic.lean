import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem clMapBasic_mem {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (τ : K ≃+* K')
    (I : Ideal (𝓞 K)) (y : 𝓞 K') :
    y ∈ I.map (RingOfIntegers.mapRingEquiv τ) ↔ ∃ x ∈ I, RingOfIntegers.mapRingEquiv τ x = y :=
  Ideal.mem_map_iff_of_surjective _ (RingOfIntegers.mapRingEquiv τ).surjective

private theorem clMapBasic_lemma {K K' K'' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    [Field K''] [NumberField K''] (τ : K ≃+* K') (τ' : K' ≃+* K'') (c : ClassGroup (𝓞 K)) :
    clMap (τ.trans τ') c = clMap τ' (clMap τ c) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [class_map_mk0, class_map_mk0, class_map_mk0]
  congr 1
  apply Subtype.ext
  show Ideal.map _ _ = Ideal.map _ (Ideal.map _ _)
  ext y
  rw [clMapBasic_mem, clMapBasic_mem]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv τ x, (clMapBasic_mem τ _ _).mpr ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (clMapBasic_mem τ _ _).mp hz
    exact ⟨x, hx, rfl⟩
private theorem clMap_refl_apply {K : Type} [Field K] [NumberField K] (c : ClassGroup (𝓞 K)) :
    clMap (RingEquiv.refl K) c = c := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [class_map_mk0]
  congr 1
  apply Subtype.ext
  show Ideal.map _ _ = _
  ext y
  rw [clMapBasic_mem]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem UpperTheory.V.Kum.clMapBasic :
    ∀ (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K''] (τ : K ≃+* K') (τ' : K' ≃+* K''),
    (∀ c, clMap (RingEquiv.refl K) c = c) ∧ (∀ c, clMap (τ.trans τ') c = clMap τ' (clMap τ c)) ∧ Function.Bijective (clMap τ) ∧
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K')), (∀ x, x ∈ v.asIdeal ↔ RingOfIntegers.mapRingEquiv τ x ∈ w.asIdeal) → clMap τ (primeCl v) = primeCl w := by
  intro K K' K'' _ _ _ _ _ _ τ τ'
  refine ⟨clMap_refl_apply, clMapBasic_lemma τ τ', ?_, ?_⟩
  · have hl : ∀ c, clMap τ.symm (clMap τ c) = c := by
      intro c
      rw [← clMapBasic_lemma, RingEquiv.self_trans_symm, clMap_refl_apply]
    have hr : ∀ c, clMap τ (clMap τ.symm c) = c := by
      intro c
      rw [← clMapBasic_lemma, RingEquiv.symm_trans_self, clMap_refl_apply]
    exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩
  · intro v w hvw
    unfold primeCl
    rw [class_map_mk0]
    congr 1
    apply Subtype.ext
    show Ideal.map _ _ = _
    ext y
    rw [clMapBasic_mem]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hvw x).mp hx
    · intro hy
      refine ⟨(RingOfIntegers.mapRingEquiv τ).symm y, ?_, ?_⟩
      · rw [hvw, RingEquiv.apply_symm_apply]
        exact hy
      · exact RingEquiv.apply_symm_apply _ y
