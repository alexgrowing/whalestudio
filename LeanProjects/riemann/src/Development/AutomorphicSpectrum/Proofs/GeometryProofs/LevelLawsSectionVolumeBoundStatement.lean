import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelLawsSectionVolumeBound
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
import Development.AutomorphicSpectrum.Statements.GeometryStatements.GoodTwistGoodTwist
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sqrt_bergman_lower_bound_le_pnorm_mul_height : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) (W : HSp D) (dict : ∀ σ : c.F →+* ℂ, GA D W → Σ k, Frame ((U σ).X k).Ψ D.R.r), CompLaws U h e → abelian₂.LevelLaws U W dict → FinVol W → ∀ (a₁ : WZ D.host.E) (Z : Comp Xo c) (n : ℕ) (ω : Fin n → Rul Xo c) (I : Type) [Fintype I] (L : HermLine (fun _ : Unit => I)) (ei : I ≃ Fin n), OntoZ U h e a₁ Z → Submodule.span c.F (Set.range ω) = cuspOn U h a₁ Z → ∀ (σ : c.F →+* ℂ) (k : (U (goodOf c σ)).Comp) (y : Frame ((U (goodOf c σ)).X k).Ψ D.R.r) (lin : Rul Xo c →ₛₗ[σ] ℂ), (∀ f, lin f = Small.goodTwist c σ (rdU (U (goodOf c σ)) f k y)) → (∀ as : Fin n → ℂ, ‖∑ j, as j * lin (ω j)‖ ^ 2 ≤ (∑ j, ∑ j', as j * starRingEnd ℂ (as j') * ipOn U W dict (xiR D) a₁ (e Z) σ (ω j) (ω j')).re * L.h (fun x => lin (ω (ei x.2))) ^ 2) → Over (U (goodOf c σ)) (e Z) k → y ∈ ((U (goodOf c σ)).X k).dom → ∀ (x0 : Frame ((U (goodOf c σ)).X k).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U (goodOf c σ)).X k)))) (t : ℝ), IsOrth ((U (goodOf c σ)).X k) x0 → IsFundSet ((U (goodOf c σ)).X k) x0 FF → 0 < t → ThA.BergLB ((U (goodOf c σ)).X k) x0 FF (laZ (U (goodOf c σ)) a₁ k) y t → (∃ j, lin (ω j) ≠ 0) ∧ 0 < ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y ∧ Real.sqrt t ≤ lieFacZ Dw (xiR D) a₁ * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y * L.h (fun x => lin (ω (ei x.2))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.berg_dual | exact GlobalTheory.CompanionTheory.Ar.Rec.berg_dual | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.berg_dual <;> assumption)
