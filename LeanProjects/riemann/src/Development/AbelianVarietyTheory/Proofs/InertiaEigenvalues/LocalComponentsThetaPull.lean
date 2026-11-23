import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteHyp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivContraLocComp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
open NumberField IsDedekindDomain Matrix Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.TheRec GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.ThetaPull

noncomputable section

namespace GlobalTheory.ConjPairLoc

theorem irred_comp {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (φ : G →* H) (hφ : Function.Surjective φ) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (MonoidHom.comp ρ φ) := by
  let e : Subrepresentation (MonoidHom.comp ρ φ : Representation ℂ G V) ≃o Subrepresentation ρ :=
    { toFun := fun W => ⟨W.toSubmodule, fun g v hv => by
        obtain ⟨g, rfl⟩ := hφ g
        exact W.apply_mem_toSubmodule g hv⟩
      invFun := fun W => ⟨W.toSubmodule, fun g v hv => W.apply_mem_toSubmodule (φ g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder

theorem equiv_apply {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (e : ρ.Equiv τ) (g : G) (x : V) :
    e.toLinearEquiv (ρ g x) = τ g (e.toLinearEquiv x) :=
  LinearMap.congr_fun (e.isIntertwining' g) x

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem gl_ext {k k' : GL (Fin a) (Af E)}
    (h : ∀ v, GeneralLinearGroup.map (pLoc E v) k = GeneralLinearGroup.map (pLoc E v) k') : k = k' := by
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun v => congrArg (fun g : GL (Fin a) (v.adicCompletion E) => g.val i j) (h v)

theorem conjFin_locGL (c : E ≃+* E) (v : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) ((conjSrc c v).adicCompletion E)) :
    GeneralLinearGroup.map (conjFin c) (locGL E a _ g) = locGL E a v (GeneralLinearGroup.map (conjLoc c v) g) := by
  refine gl_ext fun u => ?_
  have e : GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (conjFin c) (locGL E a _ g)) =
      GeneralLinearGroup.map (conjLoc c u) (GeneralLinearGroup.map (pLoc E (conjSrc c u)) (locGL E a _ g)) := by
    ext i j
    rfl
  rw [e]
  by_cases h : u = v
  · subst h
    rw [pLoc_locGL, pLoc_locGL]
  · rw [pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (conjSrc_injective c e)), map_one]

theorem map_conjLoc_surjective [IsCMField E] (v : HeightOneSpectrum (𝓞 E)) :
    Function.Surjective (GeneralLinearGroup.map (n := Fin a) (conjLoc (IsCMField.complexConj E).toRingEquiv v)) := by
  intro g
  refine ⟨GeneralLinearGroup.map (pLoc E _) (GeneralLinearGroup.map (cFin E) (locGL E a v g)), ?_⟩
  conv_rhs => rw [← pLoc_locGL v g]
  ext i j : 2
  exact congrArg (pLoc E v) (cFin_cFin _)

end GlobalTheory.ConjPairLoc

end
