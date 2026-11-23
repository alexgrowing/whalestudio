import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiConj :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D) (s : W.HidaSetting l T.L Ω), ∃ cF : G T.F Ω, ∀ g : G T.L Ω, ∃ g' : G T.L Ω, W.resP T.L Ω g' = s.c * W.resP T.L Ω g * s.c⁻¹ ∧ resLe T.F_le g' = cF * resLe T.F_le g * cF⁻¹ := by
  intro Ω _ _ _ l _ c D T s
  obtain ⟨j, hj⟩ := s.hc
  have hfixF : ∀ x : T.F, s.c (x : Ω) = x := by
    intro x
    have hr := IsTotallyReal.complexEmbedding_isReal (j.comp (algebraMap T.F Ω))
    have := RingHom.congr_fun (NumberField.ComplexEmbedding.isReal_iff.1 hr) x
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply] at this
    apply j.injective
    rw [hj]
    exact this
  have hstab : ∀ (τ : G (W.Lp T.L) Ω) (x : T.L), ∃ y : T.L, τ (x : Ω) = y := by
    intro τ x
    exact ⟨τ.restrictNormal T.L x, (AlgEquiv.restrictNormal_commutes τ T.L x).symm⟩
  let cF : G T.F Ω := AlgEquiv.ofRingEquiv (f := s.c.toRingEquiv) (fun x => hfixF x)
  refine ⟨cF, fun g => ?_⟩
  let σ : G (W.Lp T.L) Ω := s.c * W.resP T.L Ω g * s.c⁻¹
  have hσ : ∀ x : T.L, σ (x : Ω) = x := by
    intro x
    obtain ⟨y, hy⟩ := hstab s.c⁻¹ x
    have h1 : g (y : Ω) = y := g.commutes y
    have h2 : s.c (y : Ω) = x := by
      rw [← hy]
      exact mul_inv_apply (σ := s.c) (x : Ω)
    show s.c (g (s.c⁻¹ (x : Ω))) = x
    rw [hy, h1, h2]
  let g' : G T.L Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun x => hσ x)
  refine ⟨g', ?_, ?_⟩
  · ext x
    rfl
  · ext x
    rfl
