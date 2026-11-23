import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBaseDegreeSettingStrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimit
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesTelescope
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesStep
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTp
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitT
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitEps
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTpIntegrandLimit
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBoundaryPtsNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PRegAboveWeight
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBdPtsNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PParamImageNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PDivisorPreimageNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPtsBddConv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPtsMonoSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTopNPoly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.POmNPoly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuRegSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PProjSmoothAlong
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHoloInjDerivInj
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegGeomDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIsomInvariance
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsIntegrable
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsMeasurable
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTopNMixedExpand
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.POmNVbInt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTTop
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuMeasureLimit
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesLimitTVbTrunc
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesLimitTVbTail
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarChartSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTpCuspIntegrable
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBoundaryNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelPtsIntegrable
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StAPrimeChartMargin
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StNbarLeviChartReg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChartStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviChartRegularityStatementHoldsStatement
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PAPrimeChartMargin
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PAPrimeChartLevi
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PAPrimeChartLeviLocal
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PChartVelLift
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PProjHoloLocal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicInverse
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicJacobianNeZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicKernelFibre
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalFlatNotInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelPointsIntegrableStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TopMixedLimitOfResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.StokesLimitStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHoldsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

noncomputable section

namespace ModelDimension.OrbitMargin

theorem margin_of_orbit (hOrb : LocalOrbitChart.Statement) : APrimeChartMargin.Statement :=
  have hP : ProjHoloLocal.Statement :=
    ProjHoloLocal.proof hOrb (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.proof
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.proof
        GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicKernelFibre.proof
        GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CriticalFlatNotInjective.proof))
  APrimeChartMargin.proof
    (APrimeChartLevi.proof (APrimeChartLeviLocal.proof hP) (ChartVelLift.proof hP))
    (ChartVelLift.proof hP)

theorem stokes_of_statements (hOrb : LocalOrbitChart.Statement)
    (hLevi : GroundTheory.Heights₂.Heights.NineStatements.NbarLeviChartReg.Statement) (hMar : APrimeChartMargin.Statement)
    (hMPI : ModelPtsIntegrable.Statement) (hMix : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → TopNMixedLimit.Statement)
    (hVb : StokesLimitTVb.Statement) (hMuL : MuMeasureLimit.Statement) : PB.Inputs → Prov.An → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Flat.GagaSections → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → ∀ [DecidableEq (CMType H)] (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt), X.H = Hd → (∀ z ∈ Dc.Xo, X.Cd.cuspWeight z = U z) → CuspBundlePos X → ∀ B : ℕ, 4 * Dc.f + 2 ≤ B → ArLimExists X.H X.S B → Top.StokesAt X B := by
  intro h1 h2 h3 h4 h5 E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U hFull hAdm hCw _ O Lt _ _ _ X hH hU hPos B hB hAr a hyp
  have hRes : ReciprocityTheory.ChartRestriction.G.Geo.ResExistsStatement := h1.resExists
  have hInt : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement :=
    GroundTheory.Heights₂.Heights.ForSecondHalf.PtsIntegrable.of_resExists hRes
  have hG := GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.proof (GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree h1.degree)
  have hTel := StokesTelescope.proof (StokesStep.proof hRes)
  have hVP := VertFactorPos.proof
  have hVS := VertFactorSmooth.proof hVP
  have hHE := HermExtend.proof
  have hPsa := ProjSmoothAlong.proof HoloInjDerivInj.proof hOrb
  have hS := NbarSmooth.proof hHE hPsa hVS
  have hMu := MuRegSmooth.proof hHE hPsa hVS hVP
  have hIso := GroundTheory.Heights₂.Heights.HilbertSamuel.IsomInvariance.proof (GroundTheory.Heights₂.Heights.Inter.RatR.proof hInt)
  have hE := TopNMixedExpand.proof hIso hMu
  have hTP := TopNPoly.proof hIso hVP hMu
  have hLim := TpIntegrandLimit.proof BoundaryPtsNull.proof
  have hAbove := RegAboveWeight.proof (BdPtsNull.proof ParamImageNull.proof) (DivisorPreimageNull.proof ParamImageNull.proof)
  have hConv := PtsBddConv.proof (GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.proof hInt
    (GroundTheory.Heights₂.Heights.Inter.PtsAbsMeasurable.proof hRes))
  have hMono := PtsMonoSemipos.proof
  have hNs := NbarSemipos.proof (NbarChartSemipos.proof hS (GroundTheory.Heights₂.Heights.NineStatements.NbarLeviChart.of_reg hLevi) hMar)
  have hCU := TpCuspIntegrable.proof (ModelLogIntegrable.proof hMPI) BoundaryNull.proof
  have hTp := StokesLimitTp.proof hLim hAbove hCU hConv hMono
  have hT := StokesLimitT.proof hG hNs (StokesLimitTTop.proof hE (hMix h3)) hVb
  have hEps := StokesLimitEps.proof hT hTP (OmNPoly.proof hNs (OmNVbInt.proof hCU hS) hInt) hMuL
  exact StokesLimitPos.proof hG hTel hNs hTp hT hEps II (CMType H) K J Ω W Dc O Lt X B a hFull.1 hPos hB hAr hyp

theorem stokes_of_model : PB.Inputs → Prov.An → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Flat.GagaSections → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → ∀ [DecidableEq (CMType H)] (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt), X.H = Hd → (∀ z ∈ Dc.Xo, X.Cd.cuspWeight z = U z) → CuspBundlePos X → ∀ B : ℕ, 4 * Dc.f + 2 ≤ B → ArLimExists X.H X.S B → Top.StokesAt X B :=
  stokes_of_statements GlobalTheory.T.local_orbit_chart_statement_holds GlobalTheory.T.levi_chart_regularity_statement_holds (margin_of_orbit GlobalTheory.T.local_orbit_chart_statement_holds) GlobalTheory.T.model_points_integrable_statement_holds GlobalTheory.T.top_mixed_limit_of_resolution GlobalTheory.T.stokes_limit_statement_holds GlobalTheory.T.measure_limit_statement_holds

end ModelDimension.OrbitMargin

theorem ModelDimension.abelian_cm_stokes_identity : PB.Inputs → Prov.An → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Flat.GagaSections → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → ∀ [DecidableEq (CMType H)] (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt), X.H = Hd → (∀ z ∈ Dc.Xo, X.Cd.cuspWeight z = U z) → CuspBundlePos X → ∀ B : ℕ, 4 * Dc.f + 2 ≤ B → ArLimExists X.H X.S B → Top.StokesAt X B :=
  ModelDimension.OrbitMargin.stokes_of_model
