import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst

namespace LocalGlobalAboveLAlt

section Defs

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

inductive Sub : Subgroup ↥(Weil h) → Prop
  | top : Sub ⊤
  | step {U V : Subgroup ↥(Weil h)} : Sub V → U ≤ V → ⁅V, V⁆ ≤ U → U.relIndex V ≠ 0 →
      IsOpen {s : ↥(Ine (F := E) A) | ineIncl h s ∈ U} → Sub U

def Triv (y : WD h) (g : ↥(Weil h)) : Prop := y.charPol g = (X - 1) ^ y.lpDim

def Main (x y : WD h) : Prop :=
  x.lpDim = y.lpDim ∧ ∀ U : Subgroup ↥(Weil h), Sub U → (∀ g ∈ U, deg g = 0 → Triv y g) →
    (x.mono0 ↔ y.mono0) ∧ ∀ g ∈ U, x.charPol g = y.charPol g

def Rel (x y : WD h) : Prop :=
  x.lpDim = y.lpDim ∧ (x.mono0 ↔ y.mono0) ∧ ∀ U : Subgroup ↥(Weil h), Sub U → (∀ g ∈ ⁅U, U⁆, Triv y g) →
    ∀ g ∈ U, x.charPol g = y.charPol g

def PT (y : WD h) : Prop :=
  ∃ e : ℕ, e.Coprime (normV w) ∧ ∀ g : ↥(Weil h), deg g = 0 → ∀ a ∈ y.eig g, ∀ b ∈ y.eig g, a ^ e = b ^ e

end Defs

def AtAll (Q : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (_h : IsPlaceOver A w), Prop) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), Q h

def ExSub : Prop := AtAll fun h => ∀ y : WD h, ∃ U : Subgroup ↥(Weil h), Sub U ∧ U.FiniteIndex ∧ ∀ g ∈ U, deg g = 0 → Triv y g

def RelOfMain : Prop := AtAll fun h => ∀ x y : WD h, Main x y → Rel x y

def RelSymm : Prop := AtAll fun h => ∀ x y : WD h, Rel x y → Rel y x

def RelOps : Prop := AtAll fun h =>
  (∀ x : WD h, Rel x x) ∧
  (∀ x y x' y' : WD h, Rel x y → Rel x' y' → Rel (x.lpSum x') (y.lpSum y')) ∧
  (∀ x y c : WD h, c.lpDim = 1 → Rel x y → Rel (x.lpChar c) (y.lpChar c)) ∧
  ∀ (x y : WD h) (s : ℝ), Rel x y → Rel (x.lpTw s) (y.lpTw s)

def RelSize : Prop := AtAll fun h => ∀ x y : WD h, Rel x y → ∀ g : ↥(Weil h), ∀ a ∈ x.eig g, ∃ b ∈ y.eig g, ‖a‖ = ‖b‖

def RelIne : Prop := AtAll fun h => ∀ x y : WD h, Rel x y → PT y → ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g

def RelAb : Prop := AtAll fun h => ∀ x y : WD h, Rel x y → (y.unr → x.unr) ∧
  ∀ (n : ℕ) (c : Fin n → (↥(Weil h) →* ℂˣ)), (∀ g, y.charPol g = ∏ i, (X - C (c i g : ℂ))) → ∀ g, x.charPol g = y.charPol g

def RelDiag : Prop := AtAll fun {E _} _ _ _ _ _ {A _} h => ∀ x y : WD h, Rel x y →
  ∀ (n : ℕ) (c : Fin n → (↥(Ine (F := E) A) →* ℂˣ)) (b : WDRep h (Fin n → ℂ)), WD.mk b = y → b.N = 0 →
    (∀ s, b.ρ (ineIncl h s) = Matrix.toLin' (Matrix.diagonal fun i => (c i s : ℂ))) →
    ∃ a : WDRep h (Fin n → ℂ), WD.mk a = x ∧ a.N = 0 ∧
      ∀ s, a.ρ (ineIncl h s) = Matrix.toLin' (Matrix.diagonal fun i => (c i s : ℂ))

def Glob (Q : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}, WD h → WD h → Prop) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a → ∀ π : CuspSub E a, π.IsCsd → (CG.mk π).IsRegAlg →
    ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      IsGalRepOf π (quadChar E ^ a) ι r wt HT →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)), w ∈ placesOver E l → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
      (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
      ∀ rc : IrrGL (w.adicCompletion E) → WD h, IsRec h rc →
        Q (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (rc (algNorm σ))

def IwahoriBaseChange : Prop := Glob fun x y => Main x y

def LocalGlobalSubnormal : Prop := Glob fun x y => Rel x y

theorem local_global_of_iwahori (h1 : RelOfMain) (h2 : IwahoriBaseChange) : LocalGlobalSubnormal :=
  fun E Ω _ _ _ _ _ _ l _ ι a ha π hc hr r wt HT hG P AI hT w hw A hA O _ _ _ Bw hj σ hσ rc hrc =>
    h1 E Ω A w hA _ _ (h2 E Ω l ι a ha π hc hr r wt HT hG P AI hT w hw A hA O Bw hj σ hσ rc hrc)

end LocalGlobalAboveLAlt
