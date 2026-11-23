import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginRootWeightBound
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
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_origin_root_weight_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [DecidableEq (CMType H)] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b₀ : T.Comp) (lam : Top.Wt (CMType H) (Dw.p + Dw.q)) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = (T.M B b₀).coef lam 0 j) → Top.RegDominant lam → ∃ (q₀ : ℕ) (n₀ : Option (RootIx Dw) → ℤ) (ε : (T.M B b₀).Ω) (u : MRing (T.M B b₀).ι) (C s₀ : ℝ), 0 < q₀ ∧ (∀ j, (n₀ j : ℝ) = q₀ * (T.M B b₀).coef T.nu (-1) j) ∧ ε ≠ 0 ∧ ε ∈ chartLatNm (T.M B b₀).y (Top.combLine ((T.M B b₀).line 1) n₀).a 1 ∧ Small.IsFormOff (mCoordIdeal (T.M B b₀).y) u ∧ 0 ≤ C ∧ 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ z ∈ mcPts (mCoordIdeal (T.M B b₀).y), MvPolynomial.aeval z u ≠ 0 → ∀ x : ℂ, Small.HasVal (T.M B b₀).y (Top.combLine ((T.M B b₀).line 1) n₀).a ε z x → x ≠ 0 → s / q₀ * Real.log ‖x‖ + (T.M B b₀).weight (Top.scale s) (lam - s • T.nu) s z ≤ C * s + Real.log (∏ r, ((o.toTowerOrigin.Or B b₀).sing r).h z ^ n' (some r)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.good_origin_root_coefficients | exact GlobalTheory.CompanionTheory.Ar.Small.good_origin_root_coefficients | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.good_origin_root_coefficients <;> assumption)
