import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem pt_val_lt_one {Ω Ω' : Type} [Field Ω] [Field Ω'] {σ : Ω ≃+* Ω'} {A : ValuationSubring Ω}
    {A' : ValuationSubring Ω'} (hA : ∀ x, x ∈ A ↔ σ x ∈ A') (x : Ω) :
    A.valuation x < 1 ↔ A'.valuation (σ x) < 1 := by
  rw [valuation_lt_one_iff' (Ω := Ω), valuation_lt_one_iff' (Ω := Ω'), ← hA, ← map_inv₀, ← hA,
    map_eq_zero_iff _ σ.injective]

theorem UpperTheory.V.LDataCardLeFinrank.placeTransport :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (f : F →+* F') (σ : Ω ≃+* Ω'), (∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) →
      ∀ φ : G F' Ω' →* G F Ω, (∀ g x, σ (φ g x) = g (σ x)) → ∀ (v' : HeightOneSpectrum (𝓞 F')) (A' : ValuationSubring Ω'), IsPlaceOver A' v' →
      ∃ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v ∧ (∀ l : ℕ, v ∈ Above F l ↔ v' ∈ Above F' l) ∧ (∀ x, x ∈ A ↔ σ x ∈ A') ∧
        (∀ g, φ g ∈ Dec (F := F) A ↔ g ∈ Dec (F := F') A') ∧ ∀ g, φ g ∈ Ine (F := F) A ↔ g ∈ Ine (F := F') A' := by
  intro F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ f σ h φ hφ v' A' hv'
  have hne : v'.asIdeal.comap (RingOfIntegers.mapRingHom f) ≠ ⊥ := by
    intro hb
    have h1 : ((Ideal.absNorm v'.asIdeal : ℕ) : 𝓞 F) ∈ v'.asIdeal.comap (RingOfIntegers.mapRingHom f) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [hb, Ideal.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at h1
    exact v'.ne_bot h1
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨v'.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, hne⟩
  have hA : ∀ x, x ∈ A'.comap σ.toRingHom ↔ σ x ∈ A' := fun x => Iff.rfl
  generalize A'.comap σ.toRingHom = A at hA
  have hD : ∀ g, φ g ∈ Dec (F := F) A ↔ g ∈ Dec (F := F') A' := by
    intro g
    constructor
    · intro hg
      rw [mem_Dec]
      ext y
      obtain ⟨x, rfl⟩ := σ.surjective y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hφ, ← hA, ← hA, map_inv]
      exact apply_mem_iff_of_mem_Dec ((Dec (F := F) A).inv_mem hg) _
    · intro hg
      rw [mem_Dec]
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, AlgEquiv.smul_def, hA, hA, hφ]
      exact apply_mem_iff_of_mem_Dec ((Dec (F := F') A').inv_mem hg) _
  refine ⟨v, A, ?_, ?_, hA, hD, ?_⟩
  · intro x
    have e : x ∈ v.asIdeal ↔ RingOfIntegers.mapRingHom f x ∈ v'.asIdeal := Iff.rfl
    rw [e, ← hv', pt_val_lt_one hA, h]
    rfl
  · intro l
    show RingOfIntegers.mapRingHom f ((l : ℕ) : 𝓞 F) ∈ v'.asIdeal ↔ ((l : ℕ) : 𝓞 F') ∈ v'.asIdeal
    rw [map_natCast]
  · intro g
    constructor
    · intro hg
      refine ⟨(hD g).1 hg.1, fun y hy => ?_⟩
      obtain ⟨x, rfl⟩ := σ.surjective y
      rw [← hφ, ← map_sub, ← pt_val_lt_one hA]
      exact hg.2 _ ((A.valuation_le_one_iff _).2 ((hA x).2 ((A'.valuation_le_one_iff _).1 hy)))
    · intro hg
      refine ⟨(hD g).2 hg.1, fun x hx => ?_⟩
      rw [pt_val_lt_one hA, map_sub, hφ]
      exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).1 ((A.valuation_le_one_iff _).1 hx)))
