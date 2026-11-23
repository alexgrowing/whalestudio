import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.AlgebraMapSignedInvolutionQuotientDetMemSpan

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.adjKill :
    ∀ (A Γ X : Type) [CommRing A] [CommGroup Γ] [Finite Γ] [AddCommGroup X] [Module A X] (π : Representation A Γ X) (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ (z : MonoidAlgebra A Γ) (x : X), π c x = (ε : A) • x → π.asAlgebraHom z x = 0 → detR c ε z • x = 0 := by
  intro A Γ X _ _ _ _ _ π c ε hc hc1 hε z x hx hz
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (algebraMap_signedInvolutionQuotientDet_mem_span (A := A) c ε hc hc1 hε z)
  have hrel : π.asAlgebraHom (rel A c ε) x = 0 := by
    simp [rel, hx, Int.cast_smul_eq_zsmul]
  have key := congrArg (fun w => π.asAlgebraHom w x) hab
  simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, hrel, hz, map_zero,
    add_zero] at key
  rw [AlgHom.commutes, Module.algebraMap_end_apply] at key
  exact key.symm
