import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoAdicCont

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

attribute [-instance] UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing in
theorem UpperTheory.V.Ws.auCont :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (κ : Γ →* c.Oˣ), AdicCont (maximalIdeal c.O) (fun g => (κ g : c.O)) → Continuous (W.pushCh (algebraMap c.O (PadicAlgCl l)) κ) := by
  intro l _ c Γ _ _ _ κ h
  have h1 : Continuous fun g => (κ g : c.O) := ((UpperTheory.V.X.So.adicCont l c).2 Γ _).1 h
  have h2 : Continuous fun g => ((W.pushCh (algebraMap c.O (PadicAlgCl l)) κ g : (PadicAlgCl l)ˣ) : PadicAlgCl l) :=
    continuous_subtype_val.comp h1
  refine Units.continuous_iff.2 ⟨h2, ?_⟩
  refine (h2.comp continuous_inv).congr fun g => ?_
  simp only [Function.comp, map_inv]
