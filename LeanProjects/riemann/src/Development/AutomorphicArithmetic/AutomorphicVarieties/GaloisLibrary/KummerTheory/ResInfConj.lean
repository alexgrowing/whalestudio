import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.resInfConj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ) (τ : F ≃+* F) (σ : Ω ≃+* Ω), IsLift τ σ → ∀ (x : H1 (qzTw D e)) (u u' : Uinf F Ω l), (∀ y, u'.1 (σ y) = σ (u.1 y)) → resInf D e (galoisActionOnCohomology D e τ x) u' = twScal l σ e • resInf D e x u := by
  intro F Ω _ _ _ _ _ l _ D e τ σ h x u u' hu
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h z
  have hc : conjGal h u'.1 = u.1 :=
    AlgEquiv.ext fun y => by rw [conjGal_apply, hu, RingEquiv.symm_apply_apply]
  rw [galois_action_cohomology_eq_conj D e h, e₁, resInf_mk, resInf_mk, f₁, conjGS_toGS, hc]
