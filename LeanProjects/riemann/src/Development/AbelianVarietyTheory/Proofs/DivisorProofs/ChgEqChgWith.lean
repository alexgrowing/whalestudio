import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr Filter Topology

noncomputable section

namespace GlobalTheory.ArDegIndep

open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad

def chgWith {D : D7} (O : Setup D) (hm : ∀ k, Mets (O.Φ.C k) (cxSt D.what₂.LL)) (c : O.s.Comp)
    (R : Option ℝ) (u : D.what₂.Tau → Fin O.N → ℝ) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ) : ℝ :=
  ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 * lnRatio (hm c R σ (O.ex x)) (O.met.h0 c σ (O.ex x)) z

def psiOf {D : D7} {O : Setup D} {A : SlopeTestRemainingChoices O.Y} {T : Real0 O.Y} {H : Ht O.Y} (h : O.Reads A T H)
    (x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s) (R : ℝ) (u : Wt O.Y) (c : O.Y.Comp) : (T.M c).Fun :=
  fun a z => chgWith O (metsOf x' O.Φ) c (some R) u ((h.man c).ε a) ((h.man c).pt a z)

theorem phR_eq_psiOf {D : D7} {O : Setup D} {A : SlopeTestRemainingChoices O.Y} {T : Real0 O.Y} {H : Ht O.Y} (h : O.Reads A T H)
    {x : GlobalTheory.ShFam.ToroidalCompactificationData O.s} {P : PolOf x O.Φ} (hC : O.CoreWith x P) {R : ℝ} (hR : 2 ≤ R) (u : Wt O.Y)
    (c : O.Y.Comp) : (T.F c).phR R u = psiOf h x R u c := by
  funext a z
  refine ((h.an c).phR R hR u a z).trans ?_
  unfold psiOf
  rw [← hC.hm_eq]
  rfl

end GlobalTheory.ArDegIndep
