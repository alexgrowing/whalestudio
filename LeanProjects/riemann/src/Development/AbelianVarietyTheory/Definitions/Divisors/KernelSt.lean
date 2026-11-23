import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField MeasureTheory
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ChernReg GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovHt GlobalTheory.LieHt

namespace GlobalTheory.HeightParts

def KernelSt : Prop :=
  ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    (a : ChartForm p σ d) (E : ChartMap p σ d), IsKaehlerForm (AnRead.all p σ d) a → IsExph a E →
    ∀ (c : AlgChart p σ d) (Kc : Set (V d)), IsCompact Kc → Kc ⊆ c.e.target →
    ∃ C t₀ : ℝ, 0 < C ∧ 0 < t₀ ∧ ∀ y ∈ c.e.source, c.e y ∈ Kc → ∀ t : ℝ, 0 < t → t ≤ t₀ →
      Metric.ball (c.e y) (C * t) ⊆ c.e.target ∧
      (∀ ξ, a c y ξ < 1 → E c y (t • ξ) ∈ c.e.source ∧ c.e (E c y (t • ξ)) ∈ Metric.ball (c.e y) (C * t)) ∧
      ∀ f : CxPts p σ → ℝ, IntegrableOn (f ∘ c.e.symm) (Metric.ball (c.e y) (C * t)) →
        Integrable (fun ξ => f (E c y (t • ξ)) * ChernReg.cutoff (a c y ξ)) ∧
        |rho a E f y t| ≤ C / t ^ (2 * d) * ∫ v in Metric.ball (c.e y) (C * t), |f (c.e.symm v)|

def OnCore (Q : ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s), PolOf x O.Φ → Prop) : Prop :=
  ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P → 2 < D.R.f * (O.N - 1) →
    (∃ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), Nonempty (O.Reads A T H)) → Q D O x P

abbrev psi {D : D7} (O : Setup D) (x : ToroidalCompactificationData O.s) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (i : Fin O.N) :
    Pts (O.var c) σ → ℝ := phW (metsOf x O.Φ) (refMet x O.Φ) c σ (fund τ i)

def SizeSt : Prop := OnCore fun _ O x _ => ∃ C : ℝ, 0 ≤ C ∧ ∀ c σ τ i, ∀ y ∈ offBd O.Φ c σ,
  -(C * Real.log (O.met.r c σ y)) ≤ psi O x c σ τ i y ∧ psi O x c σ τ i y ≤ C

def ConstSt : Prop := OnCore fun _ O x P => CommonConst (metsOf x O.Φ) (refMet x O.Φ) P.om P.exph P.a P.K P.δ

def GradSt : Prop := OnCore fun _ O x P => ∃ C μ : ℝ, 0 ≤ C ∧ 0 ≤ μ ∧ ∀ c σ τ i (ch : AlgChart (O.var c).str σ (O.var c).dim),
  ∀ y ∈ ch.e.source, y ∈ offBd O.Φ c σ → DifferentiableAt ℝ (psi O x c σ τ i ∘ ch.e.symm) (ch.e y) ∧
    ∀ ξ : V (O.var c).dim, |fderiv ℝ (psi O x c σ τ i ∘ ch.e.symm) (ch.e y) ξ| ≤
      C * O.met.r c σ y ^ μ * Real.exp (O.met.r c σ y / 2) * √(P.om c σ ch y ξ.ofLp)

def LowSt : Prop := OnCore fun _ O x P => ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
  ∀ c σ τ (i : Fin O.N), (i : ℕ) + 1 < O.N → ∀ y,
    -(C * Real.log (Real.log (1 / t))) ≤ P.regFund c σ τ i t y ∧ P.regFund c σ τ i t y ≤ C ∧
      (y ∈ offBd O.Φ c σ → psi O x c σ τ i y ≤ P.regFund c σ τ i t y)

def HessSt : Prop := OnCore fun _ O x P => ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
  ∀ c σ τ (i : Fin O.N), (i : ℕ) + 1 < O.N → ((O.var c).an σ).SmoothOn Set.univ (P.regFund c σ τ i t) ∧
    ∀ ch : AlgChart (O.var c).str σ (O.var c).dim, ∀ y ∈ ch.e.source, ∀ ξ,
      -(C * (Real.log (Real.log (1 / t)) / Real.log (1 / t)) * P.om c σ ch y ξ) ≤
        thW (refMet x O.Φ) c σ (fund τ i) ch y ξ + ddcForm (P.regFund c σ τ i t) ch y ξ

def CloseSt : Prop := OnCore fun _ O x P => ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
  ∀ c σ τ (i : Fin O.N), (i : ℕ) + 1 < O.N → ∀ y ∈ offBd O.Φ c σ, O.met.r c σ y ≤ Real.log (1 / t) →
    P.regFund c σ τ i t y ≤ psi O x c σ τ i y + t ^ ((1 : ℝ) / 3)

def CentSt : Prop := OnCore fun _ O x _ => ∀ c σ τ (i : Fin O.N), (i : ℕ) + 1 = O.N →
  ((O.var c).an σ).SmoothOn Set.univ (extBd O.Φ (psi O x c σ τ i)) ∧
    ∀ ch : AlgChart (O.var c).str σ (O.var c).dim, ∀ y ∈ ch.e.source, ∀ ξ,
      thW (refMet x O.Φ) c σ (fund τ i) ch y ξ + ddcForm (extBd O.Φ (psi O x c σ τ i)) ch y ξ = 0

section Heights

variable {D : D7} (O : Setup D) (m : ∀ c, Mets (O.Φ.C c) (cxSt D.what₂.LL)) (y : Pt O.s)

def stepHt (τ : D.host.E →+* ℂ) (k : ℕ) : ℝ :=
  -∑ i ∈ Finset.range k, (adlOf (O.Φ.C _) (m _) (Finsupp.single (ArIn.ind ∅, none, .inl (τ, i)) 1)).ht (basePt O.Φ y)

def omHt : ℝ := (adlOf (O.Φ.C _) (m _) (detOmSym D.host.E (D.R.f * O.N))).ht (basePt O.Φ y)

def ReadsAt {K : Type} [Field K] [NumberField K] {g : ℕ} (h : HermFam K (Fin g → K)) (L : Submodule (𝓞 K) (Fin g → K))
    (C : ℝ) : Prop :=
  |deg h L + omHt O m y| ≤ C ∧ ∀ τ, ∀ k ≤ O.S.Dw.mult τ, ∃ W ≤ L, latRank K W = k ∧ |deg h W + stepHt O m y τ k| ≤ C

abbrev ref0 : ∀ c, Mets (O.Φ.C c) (cxSt D.what₂.LL) := fun c _ => O.met.h0 c

example : omHt O O.met.hm y = O.faltAt _ (basePt O.Φ y) := rfl

end Heights

def PtInt : Prop := OnObj fun D O _ _ H _ => ∃ C : ℝ, ∀ y : Pt O.s, y ∈ H.int →
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (F : SemiFib K) (h : HermFam K (Fin F.P₀.g → K)),
    F.P₀.g = D.R.f * O.N ∧ F.IsHerm h ∧ ReadsAt O O.met.hm y h F.lieLat C

def PtBd : Prop := OnObj fun D O _ _ H _ => ∃ C : ℝ, 1 ≤ C ∧ ∀ y : Pt O.s, y ∉ H.int →
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (F : SemiFib K) (h' : HermFam K (Fin F.P₀.g → K))
    (h : HermFam K (Fin (D.R.f * O.N) → K)) (L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K)) (r : ℕ)
    (ε : Fin r → Fin (D.R.f * O.N) → K) (q : (Fin (D.R.f * O.N) → K) →ₗ[K] (Fin F.P₀.g → K)),
    F.IsHerm h' ∧ ReadsAt O (ref0 O) y h L C ∧ TorusExt h L ε q h' F.lieLat C

def StepInt : Prop := OnObj fun _ O _ _ H _ => ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Pt O.s, y ∈ H.int →
  -H.falt y ≤ C * Real.log (2 + max (H.falt y) 0) ∧
    ∀ τ, ∀ k ≤ O.S.Dw.mult τ, -(C * Real.log (2 + max (H.falt y) 0)) ≤ stepHt O O.met.hm y τ k

def StepBd : Prop := OnObj fun _ O _ _ H _ => ∃ C : ℝ, 1 ≤ C ∧ ∀ y : Pt O.s, y ∉ H.int → -C ≤ H.hA y ∧
  ∀ τ, ∀ k ≤ O.S.Dw.mult τ, -(C * Real.log (2 + C + H.hA y)) - C ≤ stepHt O (ref0 O) y τ k

open Classical in

def FlatHt : Prop := OnObj fun D O _ _ H _ => ∃ C : ℝ, ∀ (τ : D.what₂.Tau) (y : Pt O.s),
  |H.h0 (fun τ' _ => if τ' = τ then 1 else 0) y| ≤ C ∧ (y ∈ H.int → |H.hH (fun τ' _ => if τ' = τ then 1 else 0) y| ≤ C)

def OmCmp : Prop := OnObj fun _ O _ _ H _ => ∃ C : ℝ, ∀ y : Pt O.s, |omHt O (ref0 O) y| ≤ C * (|H.hA y| + 1)

def FaltSt : Prop := OnObj fun _ _ _ _ H _ => HtFalt H

end GlobalTheory.HeightParts

end
