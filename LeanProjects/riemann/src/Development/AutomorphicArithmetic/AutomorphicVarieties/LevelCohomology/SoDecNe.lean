import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowNStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.DecCyc

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem one_lt_normV {k : Type} [Field k] [NumberField k] (v : HeightOneSpectrum (𝓞 k)) : 1 < normV v := by
  have h : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  rw [h]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h1 => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)
  omega

private theorem cyc_ne (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ)
    [Fact l.Prime] (v : HeightOneSpectrum (𝓞 k)) (A : ValuationSubring Ω) (hA : IsPlaceOver A v) (n : ℤ) (hn : n ≠ 0) :
    ∃ g : G k Ω, g ∈ Dec (F := k) A ∧ cycZ k Ω l g ^ n ≠ 1 := by
  by_cases hl : ((l : ℕ) : 𝓞 k) ∈ v.asIdeal
  · exact GlobalTheory.T.exists_decompositionGroup_cyclotomicCharacter_zpow_ne_one k Ω l v A hl hA n hn
  · obtain ⟨γ, hγ⟩ := exists_isFrob hA
    refine ⟨γ, hγ.1, fun h => ?_⟩
    have hc := cycZ_of_isFrob hl hA hγ
    have h2 : cycZ k Ω l γ ^ n.natAbs = 1 := by
      rcases Int.natAbs_eq n with e | e
      · rw [← zpow_natCast, ← e, h]
      · rw [e, zpow_neg, inv_eq_one, zpow_natCast] at h; exact h
    have h3 := congrArg (Units.val : ℤ_[l]ˣ → ℤ_[l]) h2
    rw [Units.val_pow_eq_pow_val, hc, Units.val_one] at h3
    have h4 : normV v ^ n.natAbs = 1 := by exact_mod_cast h3
    exact (Nat.one_lt_pow (Int.natAbs_ne_zero.2 hn) (one_lt_normV v)).ne' h4

theorem UpperTheory.V.X.So.decNe :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ψ : G k Ω →* Oˣ), IsOpen (ψ.ker : Set (G k Ω)) → ∀ n : ℤ, n ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 k)) (A : ValuationSubring Ω), IsPlaceOver A v → ∃ g ∈ Dec (F := k) A, (ψ * chiO k Ω l O ^ n) g ≠ 1 := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ ψ hψ n hn v A hA
  haveI : IsGalois k Ω := {}
  haveI : Finite (G k Ω ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hψ
  have hm : ψ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨g, hg, hne⟩ := cyc_ne k Ω l v A hA (n * (ψ.ker.index : ℤ)) (mul_ne_zero hn (Int.natCast_ne_zero.2 hm))
  refine ⟨g, hg, fun h => hne ?_⟩
  have hinj := (dvrFacts l O).1
  have h1 : ψ g ^ ψ.ker.index = 1 := by
    rw [← map_pow]; exact ψ.ker.pow_index_mem g
  have h2 : ψ g * chiO k Ω l O g ^ n = 1 := h
  have h3 : chiO k Ω l O g ^ (n * (ψ.ker.index : ℤ)) = 1 := by
    have := congrArg (· ^ ψ.ker.index) h2
    simp only [mul_pow, h1, one_mul, one_pow] at this
    rw [zpow_mul, zpow_natCast, this]
  apply Units.map_injective (f := (algebraMap ℤ_[l] O).toMonoidHom) hinj
  rw [map_zpow, map_one]
  exact h3
