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
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.YReadArchC
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormOffSpecializationRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameHeightStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.UnitarySelfGeneration

theorem y_read_arch : (Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z), ∃ u : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) u ∧ ∀ (σ : c.F →+* ℂ), ∀ z ∈ mcPts (mCoordIdeal RM.y), (∀ t : c.F, Small.HasVal RM.y 0 (Or.𝔐.cst t) z (σ t)) → MvPolynomial.aeval z u ≠ 0 → ∃ k, Over (U (goodOf c σ)) (e Z) k ∧ ∃ y ∈ ((U (goodOf c σ)).X k).dom, ∀ (a : WZ E) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) → ∃ θ : ℂ, ‖θ‖ = (∏ r', (Or.sing r').h z ^ n' (some r')) * lieFacZ Dw x a * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (fun _ => 1) y ∧ ∀ f ∈ secZ Xo c a, (GoodEmb c σ → Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z (θ * rdU (U (goodOf c σ)) f k y)) ∧ (¬ GoodEmb c σ → Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z (θ * starRingEnd ℂ (rdU (U (goodOf c σ)) f k y)))) := by
  intro _ E _ _ _ H Dw l Xo c r U h e hL x hx O _ β Y SS RM Sys Fx Or Fr Z Rd
  haveI : CharZero RM.Ω := charZero_of_injective_ringHom Or.𝔐.cst.injective
  obtain ⟨B, hB⟩ := GlobalTheory.T.root_origin_frame_height E H Dw l Xo c O β Y SS RM Sys Fx Or Fr
  obtain ⟨u, hu, hA⟩ := GlobalTheory.T.form_off_specialization_ring RM.K RM.ι RM.Ω RM.y RM.birational B
  refine ⟨u, hu, fun σ z hz hcst hzu => ?_⟩
  have hz' := RA.ptsOver_of_mcPts hz
  by_cases hσ : GoodEmb c σ
  · have eg : goodOf c σ = σ := if_pos hσ
    rw [eg]
    obtain ⟨A, ev, hBA, hQ, hev⟩ := hA ℂ z hz' hzu
    obtain ⟨-, k, hk, y, hy, hh⟩ := RA.core hL hx Rd (hB A hBA hQ) hσ hz' ev hev hcst
    refine ⟨k, hk, y, hy, fun a n' hn => ?_⟩
    obtain ⟨θ, h1, h2⟩ := hh a n' hn
    exact ⟨θ, h1, fun f hf => ⟨fun _ => h2 f hf, fun hn => absurd hσ hn⟩⟩
  · have eg : goodOf c σ = (starRingEnd ℂ).comp σ := if_neg hσ
    have hg := goodEmb_goodOf c σ
    have hcst' : ∀ t : c.F, Small.HasVal RM.y 0 (Or.𝔐.cst t) (fun p => starRingEnd ℂ (z p)) (goodOf c σ t) := fun t => by
      rw [eg]
      exact RA.hv_conj (hcst t)
    have hz'' := RA.ptsOver_conj hz'
    obtain ⟨A, ev, hBA, hQ, hev⟩ := hA ℂ _ hz'' (by rw [RA.aeval_conj]; exact (map_ne_zero _).2 hzu)
    obtain ⟨hc, k, hk, y, hy, hh⟩ := RA.core hL hx Rd (hB A hBA hQ) hg hz'' ev hev hcst'
    simp only [Complex.conj_conj] at hc
    refine ⟨k, hk, y, hy, fun a n' hn => ?_⟩
    obtain ⟨θ, h1, h2⟩ := hh a n' hn
    refine ⟨starRingEnd ℂ θ, ?_, fun f hf => ⟨fun hn => absurd hn hσ, fun _ => ?_⟩⟩
    · rw [Complex.norm_conj, h1]
      simp only [← hc]
    · have h3 := RA.hv_conj (h2 f hf)
      simp only [Complex.conj_conj, map_mul] at h3
      exact h3

end PositivityTheory.UnitarySelfGeneration
