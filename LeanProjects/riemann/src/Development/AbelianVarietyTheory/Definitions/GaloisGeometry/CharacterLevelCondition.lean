import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ArthurClozelLocalSC

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

def PlainMix {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k) : Prop :=
  ∃ s, HasSupport x.rep s ∧ (∀ y ∈ s, UpperTheory.Zero.LLC.GoodCusp y) ∧ Unlinked s

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ} [IsCMField E]

def MixAt (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), π.IsLocComp w σ → PlainMix (IrrGL.of σ.ρ σ.smooth σ.irred)

def GoodAt (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), π.IsLocComp w σ → UpperTheory.Zero.LLC.Good (IrrGL.of σ.ρ σ.smooth σ.irred)

def CharAt (unr : Bool) (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))),
    π.IsLocComp w σ → ∀ (ξ : Fin a → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)),
    HasSupport (algNorm σ).rep (chars ξ hξ) →
    (unr = true → ∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) →
    ∀ c : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h c →
      ∀ g : Weil h, (wdOf h hl ι r).charPol g = ∏ j, (X - C ((ξ j (c g) : ℂˣ) : ℂ))

def CharacterLevelCondition (unr : Bool) (s : Level) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope s l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ w, PlaceOK s w → CharAt unr π ι r w

def IwSS : Prop := CharacterLevelCondition true .csd

structure PropsM (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ)
    (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where

  away : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    MixAt π w → (wdOf h hl ι r).mono0 ∧ ∀ rc : IrrGL (w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc →
      ∀ σ, π.IsLocComp w σ → ∀ t : Ine (F := E) A, (wdOf h hl ι r).charPol (ineIncl h t) = (rc (algNorm σ)).charPol (ineIncl h t)

  sizeAway : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    MixAt π w → ∀ (g : Weil h), deg g ≠ 0 → ∀ z ∈ ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).eig g,
      ((normV w : ℕ) : ℝ) ^ (-(|(deg g : ℤ)| : ℝ) / 2) < ‖z‖ ∧ ‖z‖ < ((normV w : ℕ) : ℝ) ^ ((|(deg g : ℤ)| : ℝ) / 2)

  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), MixAt π w → GlobalTheory.NarrowPolarizedGalois.AboveN π ι r HT P h Bw hj

structure PropsG (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) : Prop where

  ine : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    GoodAt π w → ∀ rc : IrrGL (w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc →
      ∀ σ, π.IsLocComp w σ → ∀ t : Ine (F := E) A, (wdOf h hl ι r).charPol (ineIncl h t) = (rc (algNorm σ)).charPol (ineIncl h t)

  ssTor : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ, π.IsLocComp w σ →
      UpperTheory.Zero.LLC.Toral (IrrGL.of σ.ρ σ.smooth σ.irred) → ∀ g : Weil h, (wdOf h hl ι r).charPol g = (rc (algNorm σ)).charPol g

  awayIne : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    GoodAt π w → ∀ rc : IrrGL (w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ, π.IsLocComp w σ →
    ∀ (n : ℕ) (x y : WDRep h (Fin n → ℂ)), WD.mk x = wdOf h hl ι r → WD.mk y = rc (algNorm σ) →
    ∀ χ : ↥(Ine (F := E) A) → ℂ, (∀ v, (∀ s, y.ρ (ineIncl h s) v = χ s • v) → y.N v = 0) →
      ∀ v, (∀ s, x.ρ (ineIncl h s) v = χ s • v) → x.N v = 0

  size : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    GoodAt π w → ∀ (g : Weil h), deg g ≠ 0 → ∀ z ∈ ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).eig g,
      ((normV w : ℕ) : ℝ) ^ (-(|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2) < ‖z‖ ∧ ‖z‖ < ((normV w : ℕ) : ℝ) ^ ((|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2)

def RowM : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), 1 ≤ a →
    InScope .all l π χ → ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      PropsU π χ ι r wt HT → PropsM π ι r wt HT

def RowG : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), 1 ≤ a →
    InScope .all l π χ → ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      PropsU π χ ι r wt HT → PropsG π ι r wt

end GlobalTheory.RoadU

end
