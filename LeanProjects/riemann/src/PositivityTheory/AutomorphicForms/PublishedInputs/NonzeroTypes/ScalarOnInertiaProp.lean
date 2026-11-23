import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.GIface
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

def DeterminantVectorProp : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V) (η : kˣ →* ℂˣ),
    (IsSpherical ρ → HasDetVec (twist ρ (detChar (Fin N) η)) η) ∧
    (HasDetVec ρ η → IsSpherical (twist ρ (detChar (Fin N) η⁻¹)))

def UnramifiedTwistProp : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (u : WD h) (ψ : Weil h →* ℂˣ) (hψ : IsSmooth ψ), u.unr →
    (u.lpChar (WD.lpOfChar h ψ hψ)).mono0 ∧ ∀ t : Ine (F := E) A,
      (u.lpChar (WD.lpOfChar h ψ hψ)).charPol (ineIncl h t) = (X - C ((ψ (ineIncl h t) : ℂˣ) : ℂ)) ^ u.lpDim

def SumOverListProp : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (l : List (WD h)),
    ((sumList l).mono0 ↔ ∀ y ∈ l, y.mono0) ∧ ∀ σ : Weil h, (sumList l).charPol σ = (l.map fun y => y.charPol σ).prod

def IsotypicComponentProp : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (u : WD h) (s : ℕ) (d : Fin s → ℕ) (ψ : Fin s → Weil h →* ℂˣ),
    (∀ b, IsSmooth (ψ b)) → (∀ b c, b ≠ c → ∃ t : Ine (F := E) A, ψ b (ineIncl h t) ≠ ψ c (ineIncl h t)) → u.mono0 →
    (∀ t : Ine (F := E) A, u.charPol (ineIncl h t) = ∏ b, (X - C ((ψ b (ineIncl h t) : ℂˣ) : ℂ)) ^ d b) →
    ∃ v : Fin s → WD h, (∀ b, (v b).mono0 ∧ (v b).lpDim = d b ∧
      ∀ t : Ine (F := E) A, (v b).charPol (ineIncl h t) = (X - C ((ψ b (ineIncl h t) : ℂˣ) : ℂ)) ^ d b) ∧
      u = sumList (List.ofFn v)

def ScalarOnInertiaProp : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (v : WD h) (ψ : Weil h →* ℂˣ) (hψ : IsSmooth ψ), v.mono0 →
    (∀ t : Ine (F := E) A, v.charPol (ineIncl h t) = (X - C ((ψ (ineIncl h t) : ℂˣ) : ℂ)) ^ v.lpDim) →
    ∃ v' : WD h, v'.unr ∧ v'.lpDim = v.lpDim ∧ v = v'.lpChar (WD.lpOfChar h ψ hψ)

def SphericalOfUnramifiedProp : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (ε : EpsFamily A) (rc : IrrGL (w.adicCompletion E) → WD h), Laws a ha ε rc →
    ∀ (d : ℕ) (v : WD h), v.unr → v.lpDim = d →
      ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X) (σ : Representation ℂ (GL (Fin d) (w.adicCompletion E)) X)
        (hs : IsSmooth σ) (hi : σ.IsIrreducible), IsSpherical σ ∧ rc (IrrGL.of σ hs hi) = v

def SphericalUnramifiedProp : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (ε : EpsFamily A) (rc : IrrGL (w.adicCompletion E) → WD h), Laws a ha ε rc →
    ∀ (d : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (GL (Fin d) (w.adicCompletion E)) X)
      (hs : IsSmooth σ) (hi : σ.IsIrreducible), IsSpherical σ → (rc (IrrGL.of σ hs hi)).unr

def TwistRestrictionProp : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (ε : EpsFamily A) (rc : IrrGL (w.adicCompletion E) → WD h), Laws a ha ε rc →
    ∀ (d : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (GL (Fin d) (w.adicCompletion E)) X)
      (hs : IsSmooth σ) (hi : σ.IsIrreducible) (η : (w.adicCompletion E)ˣ →* ℂˣ) (hη : IsSmoothChar η),
      ∃ (hs' : IsSmooth (twist σ (detChar (Fin d) η))) (hi' : (twist σ (detChar (Fin d) η)).IsIrreducible),
        rc (IrrGL.of (twist σ (detChar (Fin d) η)) hs' hi') =
          (rc (IrrGL.of σ hs hi)).lpChar (WD.lpOfChar h (η.comp a) (ha.smooth hη))

def UntwistRestrictionProp : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (ε : EpsFamily A) (rc : IrrGL (w.adicCompletion E) → WD h), Laws a ha ε rc →
    ∀ (d : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (GL (Fin d) (w.adicCompletion E)) X)
      (hs : IsSmooth σ) (hi : σ.IsIrreducible) (η : (w.adicCompletion E)ˣ →* ℂˣ) (hη : IsSmoothChar η),
      ∃ (hs' : IsSmooth (twist σ (detChar (Fin d) η⁻¹))) (hi' : (twist σ (detChar (Fin d) η⁻¹)).IsIrreducible),
        rc (IrrGL.of σ hs hi) =
          (rc (IrrGL.of (twist σ (detChar (Fin d) η⁻¹)) hs' hi')).lpChar (WD.lpOfChar h (η.comp a) (ha.smooth hη))

def ProductRestrictionProp : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (ε : EpsFamily A) (rc : IrrGL (w.adicCompletion E) → WD h), Laws a ha ε rc →
    ∀ (s N : ℕ) (d : Fin s → ℕ) (hd : ∑ b, d b = N) (X : Fin s → Type) [∀ b, AddCommGroup (X b)] [∀ b, Module ℂ (X b)]
      (σ : ∀ b, Representation ℂ (GL (Fin (d b)) (w.adicCompletion E)) (X b)) (hs : ∀ b, IsSmooth (σ b))
      (hi : ∀ b, (σ b).IsIrreducible) (hI : (multiProd (stdBlocks d hd) σ).IsIrreducible),
      rc (IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI) =
        sumList (List.ofFn fun b => rc (IrrGL.of (σ b) (hs b) (hi b)))

def CuspidalSupportProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitLoc →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (X : Type)
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (GL (Fin d) k) X), IsSmooth σ → σ.IsIrreducible →
    ∀ η : kˣ →* ℂˣ, IsSmoothChar η → HasDetVec σ η →
      ∃ μ : Fin d → kˣ →* ℂˣ, (∀ j, IsSmoothChar (μ j) ∧ ∀ u : kˣ, valuation k (u : k) = 1 → μ j u = η u) ∧
        IsCuspSupport σ (fun _ => 1) (fun j => detRep (Fin 1) (μ j))

def ProductIrreducibleProp : Prop :=
  CuspidalSupportProp → GlobalTheory.Mem.LiteralAutomorphy.LitLoc →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s N : ℕ) (d : Fin s → ℕ)
    (hd : ∑ b, d b = N) (X : Fin s → Type) [∀ b, AddCommGroup (X b)] [∀ b, Module ℂ (X b)]
    (σ : ∀ b, Representation ℂ (GL (Fin (d b)) k) (X b)), (∀ b, IsSmooth (σ b)) → (∀ b, (σ b).IsIrreducible) →
    ∀ η : Fin s → kˣ →* ℂˣ, (∀ b, IsSmoothChar (η b)) → (∀ b, HasDetVec (σ b) (η b)) →
    (∀ b c, b ≠ c → ∃ u : kˣ, valuation k (u : k) = 1 ∧ η b u ≠ η c u) →
      (multiProd (stdBlocks d hd) σ).IsIrreducible

def ArtinInertiaProp : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
    (∀ t : Ine (F := E) A, valuation (w.adicCompletion E) ((a (ineIncl h t) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1) ∧
    ∀ u : (w.adicCompletion E)ˣ, valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 → ∃ t : Ine (F := E) A, a (ineIncl h t) = u

def GMain : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (ε : EpsFamily A) (rc : IrrGL (w.adicCompletion E) → WD h), Laws a ha ε rc → GlobalTheory.Mem.LiteralAutomorphy.LitLoc →
    ∀ (s : ℕ) (d : Fin s → ℕ) (η : Fin s → (w.adicCompletion E)ˣ →* ℂˣ), (∀ b, IsSmoothChar (η b)) →
    (∀ b c, b ≠ c → ∃ t : Ine (F := E) A, η b (a (ineIncl h t)) ≠ η c (a (ineIncl h t))) →
    ∀ (x : IrrGL (w.adicCompletion E)) (hd : ∑ b, d b = x.1),
      ((rc x).mono0 ∧ ∀ t : Ine (F := E) A,
          (rc x).charPol (ineIncl h t) = ∏ b, (X - C ((η b (a (ineIncl h t)) : ℂˣ) : ℂ)) ^ d b) ↔
        IsTwSphProd x.rep d hd η

end UpperTheory.TNZ
