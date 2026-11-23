import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.LocalGlobalCompatAtIwahoriFixedPlaces
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.GoodLiftAlt

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.ToralGalois.R2

def MixedOf : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ) (π : CuspSub E n)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), π.IsLocComp w σ →
    fixed σ.ρ (KOne (w.adicCompletion E) (Fin n)) ≠ ⊥ → Apart (algNorm σ) →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
      (rc (algNorm σ)).mono0 → UpperTheory.Gal.InertialTypesAlt.Mixed (IrrGL.of σ.ρ σ.smooth σ.irred)

def InfStep : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M] [IsTotallyComplex K]
    [IsTotallyComplex M], (Module.finrank K M).Prime → ∀ n : ℕ, 0 < n → ∀ (π : CuspSub K n) (P : CuspSub M n),
    UpperTheory.V.Published.WeakBC (UpperTheory.CBC.Cusp.cx π).sat (UpperTheory.CBC.Cusp.cx P).sat →
    ∀ τ : M →+* ℂ, (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap K M))

def InfLifts : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ), 0 < n →
    ∀ (π : CuspSub E n) (Y : UpperTheory.Gal.InertialTypesAlt.Pt E Ω n), UpperTheory.Gal.InertialTypesAlt.Lifts (UpperTheory.Gal.InertialTypesAlt.Pt.base Ω π) Y →
    ∀ τ : Y.K →+* ℂ, (CG.mk Y.π).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap E Y.K))

def RecChars : Prop :=
  ∀ (M Ω : Type) [Field M] [NumberField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω] (A : ValuationSubring Ω)
    (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A u) (n : ℕ) (T : SmIrr (GL (Fin n) (u.adicCompletion M)))
    (ξ : Fin n → ((u.adicCompletion M)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport T.ρ (chars ξ hξ) →
    (GlobalTheory.RoadU.Unlinked (chars ξ hξ) → PlainTor (algNorm T)) ∧
    ∀ rc : IrrGL (u.adicCompletion M) → WD h, UpperTheory.Zero.LLC.IsRecT h rc → ∀ a, IsLocalArtin h a → ∀ t : Ine (F := M) A,
      (rc (algNorm T)).charPol (ineIncl h t) = ∏ j, (X - C ((ξ j (a (ineIncl h t)) : ℂˣ) : ℂ))

def ToTor : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)),
    InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), π.IsLocComp w σ → IsQg w →
      UpperTheory.Gal.InertialTypesAlt.Mixed (IrrGL.of σ.ρ σ.smooth σ.irred) →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
    ∃ (X : UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fld E Ω) (P : CuspSub X.K n) (χ' : HChar (maximalRealSubfield X.K)) (u : HeightOneSpectrum (𝓞 X.K))
      (h' : IsPlaceOver A u) (T : SmIrr (GL (Fin n) (u.adicCompletion X.K))) (rc' : IrrGL (u.adicCompletion X.K) → WD h'),
      InScope .all l P χ' ∧ Weak P ι (resTo X.K r) ∧
      (∀ τ : X.K →+* ℂ, (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap E X.K))) ∧
      P.IsLocComp u T ∧ PlainTor (algNorm T) ∧ UpperTheory.Zero.LLC.IsRecT h' rc' ∧
      ∀ t : Ine (F := E) A, ∃ t' : Ine (F := X.K) A, (∀ z : Ω, (t : G E Ω) z = (t' : G X.K Ω) z) ∧
        (rc' (algNorm T)).charPol (ineIncl h' t') = (rc (algNorm σ)).charPol (ineIncl h t)

def DRDesc : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (π : CuspSub E n) (r : G E Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ w : HeightOneSpectrum (𝓞 E), (∀ A : ValuationSubring Ω, IsPlaceOver A w →
      ∃ (X : UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fld E Ω) (P : CuspSub X.K n) (u : HeightOneSpectrum (𝓞 X.K)), IsPlaceOver A u ∧
        (∀ τ : X.K →+* ℂ, (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap E X.K))) ∧
        ClauseAt .dR P ι (resTo X.K r) u) → ClauseAt .dR π ι r w

end UpperTheory.Gal.ToralGalois.R2
