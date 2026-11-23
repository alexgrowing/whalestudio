import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LengthEqAddEigen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.MemShaIffResMemAbsoluteSha

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem cE_comm {F F' : Type} [Field F] [NumberField F] [IsCMField F] [Field F'] [NumberField F']
    [IsCMField F'] (f : F ≃+* F') (x : F) : f (UpperTheory.V.cE F x) = UpperTheory.V.cE F' (f x) := by
  let φ' : F' →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply φ'.injective
  have h1 := IsCMField.complexEmbedding_complexConj F (φ'.comp f.toRingHom) x
  have h2 := IsCMField.complexEmbedding_complexConj F' φ' (f x)
  show φ' (f ((IsCMField.complexConj F) x)) = φ' ((IsCMField.complexConj F') (f x))
  rw [h2]
  exact h1

private theorem length_inf_eigen {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] (Φ : M ≃ₗ[R] M') (N : Submodule R M) (N' : Submodule R M') (hN : N.map Φ.toLinearMap = N')
    (c : Module.End R M) (c' : Module.End R M') (hc : ∀ x, Φ (c x) = c' (Φ x)) (s : R) :
    Module.length R ↥(N ⊓ c.eigenspace s) = Module.length R ↥(N' ⊓ c'.eigenspace s) := by
  have hE : (c.eigenspace s).map Φ.toLinearMap = c'.eigenspace s := by
    ext y
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, Module.End.mem_eigenspace_iff,
      Module.End.mem_eigenspace_iff]
    constructor
    · intro h
      have h' := congrArg Φ h
      rwa [hc, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_smul,
        LinearEquiv.apply_symm_apply] at h'
    · intro h
      apply Φ.injective
      rw [LinearEquiv.coe_coe, hc, LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.apply_symm_apply, h]
  have hm : (N ⊓ c.eigenspace s).map Φ.toLinearMap = N' ⊓ c'.eigenspace s := by
    rw [Submodule.map_inf _ Φ.injective, hN, hE]
  rw [← hm]
  exact (Φ.submoduleMap (N ⊓ c.eigenspace s)).length_eq

theorem UpperTheory.V.LDataCardLeFinrank.partLenCongr :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [IsCMField F] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] [IsCMField F'] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (D' : LData F' Ω' l) (f : F ≃+* F') (e : ℕ), UpperTheory.V.plusLen D e = UpperTheory.V.plusLen D' e ∧ UpperTheory.V.minusLen D e = UpperTheory.V.minusLen D' e := by
  intro F Ω _ _ _ _ _ _ F' Ω' _ _ _ _ _ _ l _ D D' f e
  obtain ⟨Φ, hΦ, hact⟩ := UpperTheory.V.LDataCardLeFinrank.H1_transport_field_iso F Ω F' Ω' l D D' f (e : ℤ)
  have hc := hact (UpperTheory.V.cE F) (UpperTheory.V.cE F') (cE_comm f)
  unfold UpperTheory.V.plusLen UpperTheory.V.minusLen UpperTheory.V.ShaPlus UpperTheory.V.ShaMinus UpperTheory.V.cAct
  exact ⟨length_inf_eigen Φ _ _ hΦ _ _ hc _, length_inf_eigen Φ _ _ hΦ _ _ hc _⟩
