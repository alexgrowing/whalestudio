import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.auChi :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (c : Coef l), W.pushCh (algebraMap c.O (PadicAlgCl l)) (chiO F Ω l c.O) = cycBar F Ω l ∧ Continuous (cycBar F Ω l) := by
  intro F Ω _ _ _ _ _ l _ c
  refine ⟨?_, ?_⟩
  · ext g
    simp only [W.pushCh, chiO, cycBar, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map,
      MonoidHom.coe_coe, RingHom.coe_comp]
    exact IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l) _
  · have h1 : Continuous (algebraMap ℚ_[l] (Qbar l)) := continuous_algebraMap ℚ_[l] (Qbar l)
    have h2 : Continuous (PadicInt.Coe.ringHom (p := l)) := continuous_subtype_val
    have h3 : Continuous ⇑((algebraMap ℚ_[l] (Qbar l)).comp (PadicInt.Coe.ringHom (p := l))) :=
      h1.comp h2
    exact (Continuous.units_map
      (((algebraMap ℚ_[l] (Qbar l)).comp (PadicInt.Coe.ringHom (p := l))) : ℤ_[l] →* Qbar l)
      h3).comp (continuous_cycZ F Ω l)
