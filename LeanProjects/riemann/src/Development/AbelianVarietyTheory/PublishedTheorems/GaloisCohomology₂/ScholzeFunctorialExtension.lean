import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsLevelProjLevelProj
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure FunctorialLaws (σ : IrrGL (w.adicCompletion E) → WD h) : Prop where

  dim : ∀ x, (σ x).lpDim = x.1

  mono0 : ∀ x, (σ x).mono0

  one : ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (χ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hχ : IsSmoothChar χ), σ (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)

  ind : ∀ (x : IrrGL (w.adicCompletion E)) (t : ℕ) (y : Fin t → IrrGL (w.adicCompletion E))
    (hd : ∑ i, (y i).1 = x.1), (∀ i, 0 < (y i).1) → IsSubquotient x.rep (prodIrr y hd) → σ x = sumList (List.ofFn fun i => σ (y i))

  twist : ∀ x χ hχ, σ (x.tw χ hχ) = (σ x).lpChar (σ (.ofChar χ hχ))

  iwahoriFixed : ∀ x : IrrGL (w.adicCompletion E), (σ x).unr → fixed x.rep (iwahori (w.adicCompletion E) (Fin x.1)) ≠ ⊥

end GlobalTheory.LocLanglands

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def ScholzeFunctorialExtension : Prop :=
  ∃ σ : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
      (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), IrrGL (w.adicCompletion E) → WD h,
    (∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
      (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), FunctorialLaws (σ E Ω A w h)) ∧
    (∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
      (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
      (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω')
      (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w'), FieldCompatible (σ E Ω A w h) (σ E' Ω' A' w' h')) ∧
    ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
      [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω)
      (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v')
      (f : v.adicCompletion K →+* v'.adicCompletion L), Continuous f →
      (∀ z : K, f (algebraMap K _ z) = algebraMap L _ (algebraMap K L z)) →
      letI : Algebra (v.adicCompletion K) (v'.adicCompletion L) := f.toAlgebra
      (Module.finrank (v.adicCompletion K) (v'.adicCompletion L)).Prime →
      (∃ s : v'.adicCompletion L ≃ₐ[v.adicCompletion K] v'.adicCompletion L, s ≠ 1) →
      ∀ (x : IrrGL (v.adicCompletion K)) (y : IrrGL (v'.adicCompletion L)), x.IsCusp →
        (∀ s : v'.adicCompletion L ≃ₐ[v.adicCompletion K] v'.adicCompletion L, s ≠ 1 → LBC.IsLBCCl s x y) →
        WDRel (RingEquiv.refl Ω) (σ K Ω A v h x) (σ L Ω A v' h' y)

end GlobalTheory.Published

end
