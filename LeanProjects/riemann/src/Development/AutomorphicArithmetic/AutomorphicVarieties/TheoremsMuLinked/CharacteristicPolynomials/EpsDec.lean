import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.PsiInj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.Det.epsDec :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)), IsPlaceOver A w → ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → (cycBar L Ω l).comp (Dec (F := L) A).subtype ≠ 1 := by
  intro l _ L Ω _ _ _ _ _ A w hw hl heq
  have hinj := UpperTheory.V.Ws.Eb.psiInj A w hw hl (n := 2)
    (![(cycBar L Ω l).comp (Dec (F := L) A).subtype, 1]) ![1, 0] 1
    (by decide) one_pos (by
      intro i g _
      fin_cases i <;> simp)
  have h01 := hinj (a₁ := 0) (a₂ := 1) (by simp [heq])
  exact absurd h01 (by decide)
