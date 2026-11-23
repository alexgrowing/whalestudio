import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecLawsH
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC GlobalTheory.Published GlobalTheory.SplitRead
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
section Laws
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
theorem recLawsH_alt {rc : IrrGL (w.adicCompletion E) → WD h} (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) :
    RecLawsH fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (H); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := H
  have hc : ∀ (χ : (w.adicCompletion E)ˣ →* ℂˣ) (c : Irr (w.adicCompletion E) 1),
      Nonempty (c.π.Equiv (detRep (Fin 1) χ)) → ∃ hχ : IsSmoothChar χ, cls (toIrrRep c) = .ofChar χ hχ := by
    rintro χ c ⟨φ⟩
    have h1 : IsSmoothChar (detChar (Fin 1) χ) := (isSmooth_ofChar_iff _).1
      ((IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).isSmooth c.smooth)
    have h2 : Continuous (Matrix.GeneralLinearGroup.scalar (R := w.adicCompletion E) (Fin 1)) :=
      Units.continuous_map (continuous_matrix fun i j => by
        rw [Subsingleton.elim i j]; simpa using continuous_id')
    have h3 : (detChar (Fin 1) χ).comp (Matrix.GeneralLinearGroup.scalar (Fin 1)) = χ := by
      refine MonoidHom.ext fun z => congrArg χ ?_
      ext; simp [Matrix.GeneralLinearGroup.scalar]
    exact ⟨h3 ▸ h1.comp _ h2, congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ⟨φ⟩)⟩
  have hmp : ∀ n (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))), Nonempty (π.ρ.Equiv π'.ρ) → cls π = cls π' :=
    fun n π π' e => congrArg (Sigma.mk n) (IrrRep.cl_eq_iff.2 e)
  refine ⟨fun n π => H.dim _, fun n π π' hg => ⟨fun e => ?_, fun e => congrArg rc (hmp n _ _ e)⟩,
    fun n π π' e => congrArg rc (hmp n _ _ e), fun r t σ τ π hπ => H.prod r t _ _ _ hπ, ?_, ?_, ?_, ?_⟩
  · have := _root_.UpperTheory.One.M.LawsM.inj H _ _ hg e
    exact IrrRep.cl_eq_iff.1 (eq_of_heq (Sigma.mk.inj this).2)
  · intro t χ c τ h1 h2
    obtain ⟨hχ, e⟩ := hc χ c h1
    rw [e, congrArg rc (hmp t (toIrrRep τ) (IrrRep.det (Fin t) χ hχ) h2), H.det, sumList, List.foldr_map, speh]
    simp [List.foldr_map, ← List.map_eq_flatMap]
  · intro n χ c π π' hg h1 h2
    obtain ⟨hχ, e⟩ := hc χ c h1
    rw [e, ← _root_.UpperTheory.One.M.LawsM.twist H (cls (toIrrRep π)) χ hχ hg]
    exact congrArg rc ((IrrGL.of_eq_of.2 h2).trans (IrrGL.tw_of π.π π.smooth π.irr χ hχ).symm)
  · intro n π
    rw [← H.sph]
    exact ⟨fixed_ne_bot_of_equiv (equivRep (toIrrRep π)).symm, fixed_ne_bot_of_equiv (equivRep (toIrrRep π))⟩
  · intro n π α hα
    have φ := equivRep (toIrrRep π)
    rw [H.sat (cls (toIrrRep π)) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩, WD.frobEig_diag]
end Laws
end UpperTheory.One.M
end
end
