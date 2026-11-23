import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem ext_cc {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω)
    (φ : F →+* ℂ) :
    ∃ (σ : G ℚ Ω) (j : Ω →+* ℂ), (∀ x, j (σ x) = starRingEnd ℂ (j x)) ∧ ∀ x : F, j x = φ x := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  haveI : Module.IsTorsionFree F Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsGalois ℚ Ω := {}
  obtain ⟨j, hj⟩ : ∃ j : Ω →+* ℂ, ∀ x : F, j x = φ x := by
    letI : Algebra F ℂ := φ.toAlgebra
    let j : Ω →ₐ[F] ℂ := IsAlgClosed.lift
    exact ⟨j.toRingHom, fun x => j.commutes x⟩
  letI : Algebra Ω ℂ := j.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.toRatAlgHom.commutes x).symm
  let cj : Ω →ₐ[ℚ] ℂ := ((starRingEnd ℂ).comp j).toRatAlgHom
  exact ⟨cj.restrictNormal' Ω, j, fun x => AlgHom.restrictNormal_commutes cj Ω x, hj⟩

theorem UpperTheory.V.Ws.fixInf :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F], ((∀ σ : G ℚ Ω, IsCC σ → σ ∈ F.fixingSubgroup) → IsTotallyReal F) ∧ ((∀ σ : G ℚ Ω, IsCC σ → σ ∉ F.fixingSubgroup) → Module.finrank ℚ F = 2 → IsCMField F) := by
  intro Ω _ _ _ F _
  refine ⟨fun h => ⟨fun w => ?_⟩, fun h h2 => ?_⟩
  · obtain ⟨σ, j, hσ, hj⟩ := ext_cc F w.embedding
    have hm := (F.mem_fixingSubgroup_iff σ).1 (h σ ⟨j, hσ⟩)
    refine InfinitePlace.isReal_iff.2 (RingHom.ext fun x => ?_)
    show starRingEnd ℂ (w.embedding x) = w.embedding x
    rw [← hj, ← hσ, hm x.1 x.2]
  · haveI : IsTotallyComplex F := ⟨fun w => by
      rw [← InfinitePlace.not_isReal_iff_isComplex]
      intro hw
      obtain ⟨σ, j, hσ, hj⟩ := ext_cc F w.embedding
      refine h σ ⟨j, hσ⟩ ((F.mem_fixingSubgroup_iff σ).2 fun x hx => j.injective ?_)
      have e : starRingEnd ℂ (w.embedding ⟨x, hx⟩) = w.embedding ⟨x, hx⟩ :=
        RingHom.congr_fun (InfinitePlace.isReal_iff.1 hw) ⟨x, hx⟩
      rw [← hj] at e
      rw [hσ]; exact e⟩
    haveI : Algebra.IsQuadraticExtension ℚ F := ⟨h2⟩
    exact IsCMField.ofCMExtension ℚ F
