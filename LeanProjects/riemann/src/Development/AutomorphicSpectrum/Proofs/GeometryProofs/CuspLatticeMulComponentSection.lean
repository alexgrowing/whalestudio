import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.FlatChernWeightEqOfIndependence
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.RegularFormsIsBundleProjectiveCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwistedDualRegularFormsFiniteCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.LineDegreeClosedFormula
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationComponentUniqueStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IndepPts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.LatMul

theorem evI_of_isBC {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (f : Rul Xo c)
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {T T' : CDVR} {io : c.F →+* T.Fr} {φ : T.Fr →+* T'.Fr} (y : IntFr Xo c T io)
    (z : IntFr Xo c T' (φ.comp io)) (h : Ref.IsBC φ y z) : evI z f = φ (evI y f) := by
  letI := io.toAlgebra
  letI := (φ.comp io).toAlgebra
  obtain ⟨p, ψ, y0, h0⟩ := y.2.1
  let φA : T.Fr →ₐ[c.F] T'.Fr := { φ with commutes' := fun _ => rfl }
  have h1 : evI y f = ψ (f p y0) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) hWD f hf p ψ y0 y.1 h0
  have h2 : evI z f = (φA.comp ψ) (f p y0) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) hWD f hf p (φA.comp ψ) y0 z.1
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ψ φA h0 h)
  rw [h2, h1]
  rfl

end GlobalTheory.CompanionTheory.Ar.Rec.LatMul

open GlobalTheory.CompanionTheory.Ar.Rec.LatMul in

theorem GlobalTheory.CompanionTheory.Ar.Rec.indicator_mul_mem_latOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ (a : WZ E) (Z : Comp Xo c) (w : Rul Xo c), w ∈ (Ref.pjSys Xo c).lat (cuspZ Xo c U a) → e Z * w ∈ latOn U h a Z := by
  intro E _ _ _ H Dw l Xo c r U h e hL hU a Z w hw
  have hI := GlobalTheory.T.valuation_component_unique E H Dw l Xo c r U h e hL
  refine (mem_latIn _ _ _ _).2 ⟨(hI.2.2 a).1 Z w hw.1, ?_⟩
  rintro la _ ⟨⟨q, T, io, e', ho, y, hy, eta, heta, rfl⟩, rfl⟩
  have hv : ∃ Z₀, _ := hI.1 la _ ⟨⟨_, T, io, e', ho, y, hy, eta, heta, rfl⟩, rfl⟩
  obtain ⟨T', φV, φ, r', z, t, hfin, hbc, hz, hphi⟩ := hU la T io e' ho y hy
  have hw0 : (0 : EReal) ≤ nval T.V e' (evI y w) := by
    have h0 := hw.2 la (show (Ref.pjSys Xo c).Pt la from PtV.mk la (hfin.overLa ho) z hz t hphi)
    rw [Ref.pjSys_val_mk Xo c la (hfin.overLa ho) z hz t hphi w,
      evI_of_isBC hL.evalWD w hw.1.1.1 y z hbc, hfin.nval_eq] at h0
    exact h0
  obtain ⟨Z₀, h0, h1⟩ := hv
  let p : PtV Xo c (algCls Xo c) Unit (fun _ _ _ _ => True) la := PtV.mk la ho y hy eta heta
  have hmul : vAtV p (e Z * w) =
      vAtV p (e Z) + nval T.V e' (evI y w) := vAtV_mul _ _ _
  show (0 : EReal) ≤ vAtV p (e Z * w)
  rw [hmul]
  by_cases hZ : Z = Z₀
  · subst hZ
    have h0' : vAtV p (e Z) = 0 := h0
    rw [h0', zero_add]
    exact hw0
  · have h1' : vAtV p (e Z) = ⊤ := (h1 Z hZ).1
    rw [h1', EReal.top_add_of_ne_bot (nval_ne_bot _ _)]
    exact le_top
