import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.InsideRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenOf

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo

section Defs

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a dd : ℕ}

omit [NumberField E] [IsAlgClosure E Ω] in

def IsPiece (H : HTower E) (θ : H.Γ → Qbar l) (ρ : G E Ω →* GL (Fin dd) (Qbar l)) : Prop :=
  ∃ ρ₀ : G E Ω →* GL (Fin dd) (Qbar l), IsMat l H Ω (Qbar l) θ ρ₀ ∧ IsGr ρ₀ ρ

def HasRoots (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϑ : ℕ → Qbar l) (R : Multiset ℂ) : Prop :=
  ϑ 0 ≠ 0 ∧ (heckePol (normV w) n ϑ).map ι.toRingHom = C (ι (ϑ 0)) * rootPol R

def PhiK (ι : Qbar l ≃+* ℂ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (R : Multiset ℂ) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw),
    IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧ ∃ g : Weil h, deg g = -1 ∧ ∃ m : ℕ,
      (wdAt P ι Bw h hj (ρ.comp (Dec (F := E) A).subtype)).charPol g ∣ rootPol R ^ m

def JOcc (ι : Qbar l ≃+* ℂ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (Q : (E →+* ℂ) → ℤ → Prop) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Induces Bw →
      ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        ∃ J : Multiset ℤ, IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ J ∧ ∀ j, Q (ι.toRingHom.comp τ) j → j ∈ J

omit [NumberField E] in

def HodgeAt (ι : Qbar l ≃+* ℂ) (H : HTower E) (θ : H.Γ → Qbar l) (τ : E →+* ℂ) (j : ℤ) : Prop :=
  ∃ b : ℕ, (b : ℤ) = j ∧ HOcc (bcAlong H τ) (fun g => ι (θ g)) b

def OneK (x : E) (w w' : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ y : 𝓞 E, (y : E) ∈ IntermediateField.adjoin ℚ {x} → (y ∈ w.asIdeal ↔ y ∈ w'.asIdeal)

variable [IsCMField E]

def CongFor (ι : Qbar l ≃+* ℂ) (a : ℕ) (H : HTower E) (θ : H.Γ → Qbar l) (κ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  κ.UnrAt w ∧ ∃ ϑ : ℕ → Qbar l, CongAtW H θ w a ϑ ∧
    HasRoots ι w a ϑ ((algSat a (normV w) B).map (· * ((κ.val w : ℂˣ) : ℂ)⁻¹))

structure Pack (ι : Qbar l ≃+* ℂ) (d : ℕ) (U : Submodule ℂ (UA E a → ℂ)) : Type 1 where
  H : HTower E
  θ : H.Γ → Qbar l
  κ : HChar E
  m : (E →+* ℂ) → ℤ
  nice : Nice H
  alg : IsAlgPos κ m
  cong : ∃ X : Finset (HeightOneSpectrum (𝓞 E)), ∀ w, w ∉ X → UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, SatU U w B → CongFor ι a H θ κ w B

variable {ι : Qbar l ≃+* ℂ} {d : ℕ} {U : Submodule ℂ (UA E a → ℂ)}

def Pack.HodgeTrAt (P : Pack ι d U) (v : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ τ : E →+* ℂ, OverPl ι τ v → ∃ σ : ℂ ≃+* ℂ, ∀ lam, HasWeightAt U τ lam → ∀ j ∈ GlobalTheory.RoadWGeo.wtJumps lam,
    HodgeAt (ι.trans σ) P.H P.θ (σ.toRingHom.comp τ) (j + P.m τ)

def Pack.HTFor (P : Pack ι d U) (v : HeightOneSpectrum (𝓞 E)) : Prop := P.κ.UnrAt v ∧ GoodAtW P.H P.θ v ∧ P.HodgeTrAt v

def Pack.CongAll (P : Pack ι d U) (w : HeightOneSpectrum (𝓞 E)) : Prop := ∀ B, SatU U w B → CongFor ι a P.H P.θ P.κ w B

end Defs

def GeoOne : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (a : ℕ), Odd a → ∀ d : ℕ, FieldOK E l d → ∀ x : E, x ^ 2 = -(d : E) →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal → Apart v' w₀ → OneK x w₀ v' →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 E))) (U : Submodule ℂ (UA E a → ℂ)), AutOffT T U → GlobalTheory.CongW.TyEll E l a w₀ U → SphOffU w₀ S U →
    (∃ B, SatU U v' B) → LacWtAt ι v' U →
    (∃ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), VBase ι d U ρ) ∧
    (∀ w, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → (∃ B, SatU U w B) →
      ∃ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), VBase ι d U ρ ∧ ∀ B, SatU U w B → ESAt ι ρ w (algSat a (normV w) B)) ∧
    ∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → OneK x w v' → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) →
      (∃ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), VBase ι d U ρ ∧ CrysAt ρ w ∧ JumpsOcc U ι ρ w) ∧
      ∃ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), VBase ι d U ρ ∧ ∀ B, SatU U w B → PhiKilled ι ρ w a B

def PackEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (a : ℕ), Odd a → ∀ d : ℕ, FieldOK E l d → ∀ x : E, x ^ 2 = -(d : E) →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal → Apart v' w₀ → OneK x w₀ v' →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 E))) (U : Submodule ℂ (UA E a → ℂ)), AutOffT T U → GlobalTheory.CongW.TyEll E l a w₀ U → SphOffU w₀ S U →
    (∃ B, SatU U v' B) →
    (∃ P : Pack ι d U, P.HTFor v') ∧
    (∀ w, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → (∃ B, SatU U w B) → ∃ P : Pack ι d U, P.HTFor v' ∧ P.CongAll w) ∧
    ∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → OneK x w v' → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) →
      (∃ P : Pack ι d U, P.HTFor v' ∧ P.HTFor w) ∧ ∃ P : Pack ι d U, P.HTFor v' ∧ P.CongAll w

def RepEx : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (H : HTower E) (θ : H.Γ → Qbar l), Nice H →
    ∃ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), Continuous ρ ∧ IsSSRep ρ ∧ IsPiece H θ ρ

def ESStep : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (H : HTower E) (θ : H.Γ → Qbar l), Nice H → ∀ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), Continuous ρ → IsPiece H θ ρ →
    ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (n : ℕ) (ϑ : ℕ → Qbar l) (R : Multiset ℂ), CongAt H θ w n ϑ → HasRoots ι w n ϑ R → ESAt ι ρ w R

def CrysStep : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (H : HTower E) (θ : H.Γ → Qbar l), Nice H → ∀ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), Continuous ρ → IsPiece H θ ρ →
    ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∀ C : Cover H θ (Ow w), C.Onto → CrysAt ρ w

def JumpStep : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (H : HTower E) (θ : H.Γ → Qbar l), Nice H → ∀ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), Continuous ρ → IsPiece H θ ρ →
    ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → GoodAt H θ w → JOcc ι ρ w (HodgeAt ι H θ)

def PhiStep : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (H : HTower E) (θ : H.Γ → Qbar l), Nice H → ∀ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), Continuous ρ → IsPiece H θ ρ →
    ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∀ (n : ℕ) (ϑ : ℕ → Qbar l) (R : Multiset ℂ), CongAt H θ w n ϑ → HasRoots ι w n ϑ R → PhiK ι ρ w R

def CutStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (L : Type) [Field L] (H : HTower E) (θ : H.Γ → L), Nice H → ∀ w : HeightOneSpectrum (𝓞 E),
    (GoodAtW H θ w → GoodAt H θ w) ∧ ∀ (n : ℕ) (ϑ : ℕ → L), CongAtW H θ w n ϑ → CongAt H θ w n ϑ

def TwES : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)) (χ : G E Ω →* (Qbar l)ˣ), Continuous ρ → Continuous χ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (c : ℂ) (m : (E →+* ℂ) → ℤ), Cl ι (rk1 χ) w {c} (fun τ => {m (ι.toRingHom.comp τ)}) →
    ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ R : Multiset ℂ, ESAt ι ρ w R → ESAt ι (tw ρ χ) w (R.map (· * c))

def TwCrys : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)) (χ : G E Ω →* (Qbar l)ˣ), Continuous ρ → Continuous χ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (c : ℂ) (m : (E →+* ℂ) → ℤ), Cl ι (rk1 χ) w {c} (fun τ => {m (ι.toRingHom.comp τ)}) →
    CrysAt ρ w → CrysAt (tw ρ χ) w

def TwJ : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)) (χ : G E Ω →* (Qbar l)ˣ), Continuous ρ → Continuous χ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (c : ℂ) (m : (E →+* ℂ) → ℤ), Cl ι (rk1 χ) w {c} (fun τ => {m (ι.toRingHom.comp τ)}) →
    ∀ Q : (E →+* ℂ) → ℤ → Prop, JOcc ι ρ w Q → JOcc ι (tw ρ χ) w fun τ j => Q τ (j - m τ)

def TwPhi : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)) (χ : G E Ω →* (Qbar l)ˣ), Continuous ρ → Continuous χ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (c : ℂ) (m : (E →+* ℂ) → ℤ), Cl ι (rk1 χ) w {c} (fun τ => {m (ι.toRingHom.comp τ)}) →
    ∀ R : Multiset ℂ, PhiK ι ρ w R → PhiK ι (tw ρ χ) w (R.map (· * c))

def PhiOf : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (B : Multiset ℂˣ),
    B.card = a → PhiK ι ρ w (algSat a (normV w) B) → PhiKilled ι ρ w a B

def SatCard : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ),
    SatU U w B → B.card = a

def JumpsOf : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a dd : ℕ) (U : Submodule ℂ (UA E a → ℂ)) (ρ : G E Ω →* GL (Fin dd) (Qbar l)) (w : HeightOneSpectrum (𝓞 E))
    (Q : (E →+* ℂ) → ℤ → Prop),
    (∀ τ : E →+* ℂ, OverPl ι τ w → ∀ lam, HasWeightAt U τ lam → ∀ j ∈ GlobalTheory.RoadWGeo.wtJumps lam, Q τ j) → JOcc ι ρ w Q → JumpsOcc U ι ρ w

def RichOf : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a dd : ℕ) (U : Submodule ℂ (UA E a → ℂ)) (ρ : G E Ω →* GL (Fin dd) (Qbar l)) (v : HeightOneSpectrum (𝓞 E)),
    ((l : ℕ) : 𝓞 E) ∈ v.asIdeal → LacWtAt ι v U → JumpsOcc U ι ρ v → HTRichEx ρ a

end UpperTheory.Gal.Int.Geo

end
