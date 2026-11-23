import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.GoodLiftAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong

namespace UpperTheory.Gal.NearKilling

structure CmExt (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] where
  K : Type
  [field : Field K]
  [numberField : NumberField K]
  [isCM : IsCMField K]
  [algE : Algebra E K]
  [algΩ : Algebra K Ω]
  [tower : IsScalarTower E K Ω]
  [closure : IsAlgClosure K Ω]

attribute [instance] CmExt.field CmExt.numberField CmExt.isCM CmExt.algE CmExt.algΩ CmExt.tower CmExt.closure

instance (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] : Inhabited (CmExt E Ω) :=
  ⟨{ K := E }⟩

def GoodLiftC : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l a : ℕ) [Fact l.Prime],
    1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ w : HeightOneSpectrum (𝓞 E),
    ∃ (X : CmExt E Ω) (P : CuspSub X.K a) (χ' : HChar (maximalRealSubfield X.K)),
      InertialTypesAlt.Lifts (InertialTypesAlt.Pt.base Ω π) ({ K := X.K, π := P } : InertialTypesAlt.Pt E Ω a) ∧ InScope .good l P χ' ∧
      (∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ g ∈ Dec (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g) ∧
        ∀ w' : HeightOneSpectrum (𝓞 X.K), IsPlaceOver A w' → IsSplitAt w') ∧
      ∀ (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K))

def PolBC : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub K a) (P : CuspSub M a) (χ : HChar (maximalRealSubfield K)), GlobalTheory.ContraPair.PolarizedPair π χ →
    UpperTheory.V.Published.WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    (∃ χ' : HChar (maximalRealSubfield M), GlobalTheory.ContraPair.PolarizedPair P χ') ∧
      (χ = quadChar K ^ a → GlobalTheory.ContraPair.PolarizedPair P (quadChar M ^ a))

def WeakRes : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] [Field Ω]
    [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub K a) (P : CuspSub M a), UpperTheory.V.Published.WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ r : G K Ω →* GL (Fin a) (Qbar l), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res K Ω M))

def StepLift : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] [Field Ω]
    [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] [IsGalois K M],
    (Module.finrank K M).Prime → ∀ (l a : ℕ) [Fact l.Prime], 1 ≤ a →
    ∀ (π : CuspSub K a) (χ : HChar (maximalRealSubfield K)), InScope .all l π χ →
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v →
      (∃ τ ∈ Ine (F := K) A, ¬ UnramifiedFromSplittingCriterion.Fixes (F := K) M τ) → (∃ B, (CG.mk π).HasSat v B) →
    ∃ (P : CuspSub M a) (χ' : HChar (maximalRealSubfield M)),
      UpperTheory.V.Published.WeakBC (UpperTheory.CBC.Cusp.cx π).sat (UpperTheory.CBC.Cusp.cx P).sat ∧
      UpperTheory.CBC.SplitLift (UpperTheory.CBC.Cusp.cx π) (UpperTheory.CBC.Cusp.cx P) ∧ InScope .all l P χ' ∧
      (χ = quadChar K ^ a → GlobalTheory.ContraPair.PolarizedPair P (quadChar M ^ a)) ∧
      ∀ (ι : Qbar l ≃+* ℂ) (r : G K Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res K Ω M))

end UpperTheory.Gal.NearKilling
