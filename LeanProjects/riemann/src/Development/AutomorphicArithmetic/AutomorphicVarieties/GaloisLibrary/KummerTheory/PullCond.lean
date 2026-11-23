import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtSurj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.pullCond :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (hU : U ≤ galOf F K Ω) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (τ : K ≃+* K) (σ : Ω ≃+* Ω) (T : M →ₗ[R] M) (θ : ClassGroup (𝓞 K) → M), galOf F K Ω ≤ U → IsLift τ σ → (θ ∈ clCond K σ T ↔ clPull K hU R M θ ∈ conjCond U σ T) := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U hU R M _ _ _ τ σ T θ hU' h
  constructor
  · intro hθ u u' huu
    have e : conjGal h (toGal K hU u') = toGal K hU u :=
      AlgEquiv.ext fun x => σ.injective ((apply_conjGal h _ x).trans (huu x))
    rw [clPull_apply, clPull_apply, artConj K Ω τ σ h (toGal K hU u'), e]
    exact hθ τ h _
  · intro hφ τ' h' c
    obtain ⟨g, rfl⟩ := (artSurj K Ω).1 c
    have e : conjGal h' (conjGal h'.symm g) = g := AlgEquiv.ext fun x => by
      show σ.symm (σ (g (σ.symm (σ x)))) = g x
      rw [σ.symm_apply_apply, σ.symm_apply_apply]
    have k := hφ ⟨galEmb F K Ω g, hU' (galEmb_mem F K Ω g)⟩
      ⟨galEmb F K Ω (conjGal h'.symm g), hU' (galEmb_mem F K Ω _)⟩ fun x => by
        show σ (g (σ.symm (σ x))) = σ (g x)
        rw [σ.symm_apply_apply]
    have k' : θ (artCl K Ω (conjGal h'.symm g)) = T (θ (artCl K Ω g)) := k
    rw [artConj K Ω τ' σ h' (conjGal h'.symm g), e] at k'
    exact k'
