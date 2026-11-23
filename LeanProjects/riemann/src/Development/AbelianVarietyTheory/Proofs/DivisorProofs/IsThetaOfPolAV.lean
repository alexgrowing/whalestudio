import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm
open GlobalTheory.CechPic (cls lam)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart moeb ChernIsFlat)
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.ThetaRR

section Scheme

variable {k : Type} [CommRing k] {S : Scheme.{0}}

def IsTheta (P : PPAS S) (L : LB P.A.left) : Prop :=
  ∃ hL : L.IsLB, Out.Rigidified P.A L ∧ Out.Sym P.A L ∧ Out.RelAmple P.A L ∧ Out.KTriv P.A L ∧
    P.c = lam (cls L hL) (fst P.A P.A) (snd P.A P.A)

def IsTheta.polAV {P : PPAS S} {L : LB P.A.left} (h : IsTheta P L) : Out.PolAV S :=
  ⟨P.A, P.isAb, P.g, P.smoothDim, L, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

def dbl (P : PPAS S) : P.A.left ⟶ P.A.left := (Out.mulA P.A 2).left

theorem dbl_hom (P : PPAS S) : dbl P ≫ P.A.hom = P.A.hom := Over.w _

theorem dbl_comp (P : PPAS S) (p : S ⟶ Sp k) : dbl P ≫ (P.A.hom ≫ p) = P.A.hom ≫ p := by
  rw [← Category.assoc, dbl_hom]

variable {p : S ⟶ Sp k}

def FramedCharts (P : PPAS S) (h : VMetric p (omega P.A) P.g) (L : HermLB (P.A.hom ≫ p)) : Prop :=
  ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ)
    (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ) (j : Fl P.g → Pt (V 1) P.g → ℂ)
    (m : Pt (V 1) P.g → ℝ), y ∈ c.e.source ∧ Convex ℝ c.e.target ∧ IsPeriodChart h c τ ex ∧
      IsFramed L c.e.target τ ex j m ∧ IsDatum c.e.target τ (stdLat P.g) j m

def FlatCharts (P : PPAS S) (h : VMetric p (omega P.A) P.g) (L : HermLB (P.A.hom ≫ p)) : Prop :=
  ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ)
    (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ) (j : Fl P.g → Pt (V 1) P.g → ℂ)
    (m : Pt (V 1) P.g → ℝ), y ∈ c.e.source ∧ Convex ℝ c.e.target ∧ IsPeriodChart h c τ ex ∧
      IsFramed L c.e.target τ ex j m ∧ IsDatum c.e.target τ (stdLat P.g) j m ∧
      ChernIsFlat c.e.target τ m

end Scheme

def Naturality : Prop :=
  BaseChange ∧ OneVector ∧ IsometryInv ∧ TranslationInv ∧ SymplecticInv ∧ CoverSum ∧ FlatAcyclic

variable {g : ℕ}

def actB (γ : IndefiniteRowSideFullHecke.SiegelReframe.Sp g) (s : symMat g) : symMat g := symPart (moeb γ (tauU s))

def sdens (τ Z : Matrix (Fin g) (Fin g) ℂ) : ℝ :=
  ((τ.map fun t => (t.im : ℂ))⁻¹ * Z * (τ.map fun t => (t.im : ℂ))⁻¹ * Z.map star).trace.re

example : sdens (g := 1) (Matrix.diagonal fun _ => Complex.I) 1 = 1 := by
  have e : ((Matrix.diagonal fun _ : Fin 1 => Complex.I).map fun t => (t.im : ℂ)) = 1 := by
    ext i j; fin_cases i; fin_cases j; simp
  simp [sdens, e]

variable (g) in

def IsUnivTorsion (s v : symMat g) (T : Ext (1 + 1)) : Prop :=
  ∃ (j : Fl g → Pt (symMat g) g → ℂ) (m : Pt (symMat g) g → ℝ),
    IsDatum (siegel g) tauU (stdLat g) j m ∧ ChernIsFlat (siegel g) tauU m ∧
      IsTorsionForm tauU (stdLat g) j m ![v] s T

variable (g) in

def IsHermFun (F : symMat g → symMat g → Ext (1 + 1)) : Prop :=
  ContinuousOn (fun x : symMat g × symMat g => F x.1 x.2) (siegel g ×ˢ univ) ∧
  ∀ s ∈ siegel g, (∃ t : ℝ, ∀ v, F s v ∅ = t) ∧ ∃ B : symMat g → symMat g → ℂ,
    (∀ (a : ℂ) v v' w, B (a • v + v') w = a * B v w + B v' w) ∧ (∀ v w, B w v = star (B v w)) ∧
      ∀ v, F s v Finset.univ = Complex.I * B v v

def IsInvFun (F : symMat g → symMat g → Ext (1 + 1)) (γ : IndefiniteRowSideFullHecke.SiegelReframe.Sp g) : Prop :=
  ∀ s ∈ siegel g, ∀ v, F (actB γ s) (fderiv ℂ (actB γ) s v) = F s v

end GlobalTheory.ThetaRR
