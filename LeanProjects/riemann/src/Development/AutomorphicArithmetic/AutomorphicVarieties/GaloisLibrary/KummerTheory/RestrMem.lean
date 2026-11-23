import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.restrMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) (U V : Subgroup (G F Ω)) (h : U ≤ V) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (ρ : Representation R (G F Ω) M), (XDual N V R M).map (restr R M h) ≤ XDual N U R M ∧ (EqHom N V ρ).map (restr R M h) ≤ EqHom N U ρ ∧ ∀ (σ : Ω ≃+* Ω) (s : R), (EqEig N V ρ σ s).map (restr R M h) ≤ EqEig N U ρ σ s := by
  intro F Ω _ _ _ _ _ N U V h R M _ _ _ ρ
  have hX : ∀ φ ∈ XDual N V R M, restr R M h φ ∈ XDual N U R M := by
    intro φ hφ
    obtain ⟨h1, h2, h3, h4⟩ := hφ
    refine ⟨h1.comp_continuous (f := Subgroup.inclusion h) (continuous_inclusion h), fun a b => ?_, fun A u hu => ?_,
      fun A hA u hu => ?_⟩
    · exact h2 (Subgroup.inclusion h a) (Subgroup.inclusion h b)
    · exact h3 A (Subgroup.inclusion h u) hu
    · exact h4 A hA (Subgroup.inclusion h u) hu
  have hC : ∀ (σ : Ω ≃+* Ω) (T : M →ₗ[R] M), ∀ φ ∈ conjCond V σ T, restr R M h φ ∈ conjCond U σ T := by
    intro σ T φ hφ u u' hu
    exact hφ (Subgroup.inclusion h u) (Subgroup.inclusion h u') hu
  have hE : ∀ φ ∈ EqHom N V ρ, restr R M h φ ∈ EqHom N U ρ := by
    intro φ hφ
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hφ
    refine Submodule.mem_inf.2 ⟨hX φ h1, (Submodule.mem_iInf _).2 fun g => ?_⟩
    exact hC _ _ φ ((Submodule.mem_iInf _).1 h2 g)
  refine ⟨?_, ?_, fun σ s => ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact hX φ hφ
  · rintro _ ⟨φ, hφ, rfl⟩
    exact hE φ hφ
  · rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hφ
    exact Submodule.mem_inf.2 ⟨hE φ h1, hC _ _ φ h2⟩
