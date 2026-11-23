import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.solvable_polarized_restriction :
    UpperTheory.V.Af.Sol.PolRes := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι n r h
  obtain ⟨F₀, i1, i2, i3, i4, i5, i6, hF, μ, c, P, hμ, hs, hc, hp⟩ := h
  letI : Algebra F₀ M := ((algebraMap K M).comp (algebraMap F₀ K)).toAlgebra
  haveI : IsScalarTower F₀ K M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower F₀ M Ω := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply F₀ K Ω,
      IsScalarTower.algebraMap_apply K M Ω]
  refine ⟨F₀, i1, i2, inferInstance, inferInstance, this, i6, hF, μ, c, P, hμ, hs, hc, ?_⟩
  unfold IsPairing at hp ⊢
  intro t t' ht
  have e1 : ∀ u : G M Ω,
      AlgEquiv.restrictScalars F₀ (resG K M Ω u) = AlgEquiv.restrictScalars F₀ u := by
    intro u; ext x; rfl
  have e2 : ∀ u : G M Ω, resG F₀ M Ω u = resG F₀ K Ω (resG K M Ω u) := by
    intro u; ext x; rfl
  have key := hp (resG K M Ω t) (resG K M Ω t') (by rw [e1, e1]; exact ht)
  simpa [e2] using key
