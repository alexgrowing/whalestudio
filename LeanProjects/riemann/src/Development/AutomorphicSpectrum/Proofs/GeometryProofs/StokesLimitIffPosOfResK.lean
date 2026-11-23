import Mathlib
import Development.AutomorphicSpectrum.ParallelStatements.ParallelGeometry.StokesLimitBound
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuRegSmooth
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PMUcSmooth
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.BRegWeightLevi
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PProjSmoothAlong
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHoloInjDerivInj
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuHomMassIntegrable
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuHomCuspIntegrable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ArithSystem
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuHomDensityNonneg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuSheetLeviNonneg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PSheetChartHolo
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PRefAlongSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatementStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeAndCoordinatesOfResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChartStatement
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimit
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesTelescope
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesStep
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTp
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitT
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitEps
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTpIntegrandLimit
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PRegAboveWeight
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBdPtsNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PParamImageNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PDivisorPreimageNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPtsBddConv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPtsMonoSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.POmNPoly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTopNMixedExpand
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.POmNVbInt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarChartSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBoundaryNull
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PMUcChartSemipos
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PMUcLeviChart
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PAPrimeMarginCharts
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PChartVelLiftCharts
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PAPrimeChartLevi
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PAPrimeChartLeviLocal
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeEqGeometricDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelPointsIntegrableStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TopMixedLimitOfResolution
import Development.AutomorphicSpectrum.Proofs.MetricProofs.StokesLimitStatementHolds

noncomputable section

namespace GlobalTheory.CompanionTheory.StokesCompare

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.StokesLimitBound

section Clauses

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

def localDataToSetting_of_scaleMove (H : HodgeData D) (Cd : CuspData D O Lt) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine H))
    (S' : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorr H Cd)) (hS : S.IsTied) (hS' : S'.IsTied) : ComponentSetting D O Lt :=
  ⟨H, Cd, M, S, hS, S', hS', 1, 0⟩

end Clauses

def StatementFull : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (a : ℝ),
    IsFullIntersectionSystem II → 4 * D.f + 2 ≤ B → ArLimExists X.H X.S B → StokesLimit.Hyp X B a →
      ((D.n + 1 : ℕ) : ℝ) * (a - meanU X.H X.Cd / 2) * degMu X.H ≤ arLim X.H X.S B

def StatementDefined : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (a : ℝ),
    IsFullIntersectionSystem II → MeanDefined X.H X.Cd → SmoothAtSmallScale X.H X.Cd X.S X.S' B →
    4 * D.f + 2 ≤ B → ArLimExists X.H X.S B → StokesLimit.Hyp X B a →
      ((D.n + 1 : ℕ) : ℝ) * (a - meanU X.H X.Cd / 2) * degMu X.H ≤ arLim X.H X.S B

def StatementPos : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (a : ℝ),
    IsIntersectionSystem II → 0 < degMu X.H →
    4 * D.f + 2 ≤ B → ArLimExists X.H X.S B → StokesLimit.Hyp X B a →
      ((D.n + 1 : ℕ) : ℝ) * (a - meanU X.H X.Cd / 2) * degMu X.H ≤ arLim X.H X.S B

def StatementNonpos : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (a : ℝ),
    IsIntersectionSystem II → degMu X.H ≤ 0 →
    4 * D.f + 2 ≤ B → ArLimExists X.H X.S B → StokesLimit.Hyp X B a →
      ((D.n + 1 : ℕ) : ℝ) * (a - meanU X.H X.Cd / 2) * degMu X.H ≤ arLim X.H X.S B

section Mass

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Giv.MuLimit

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem degMu_nonneg (X : ComponentSetting D O Lt) : 0 ≤ degMu X.H := by
  classical
  have hN := MuHomDensityNonneg.proof (MuSheetLeviNonneg.proof SheetChartHolo.proof RefAlongSheet.proof)
  have hdeg : degMu X.H = ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu X.H) (fun _ => 1) := rfl
  rw [hdeg]
  unfold ptsIntegral
  split_ifs with hΨ
  · refine integral_nonneg_of_ae ?_
    filter_upwards [hN II Ψ K ι Ω E D O Lt X _ hΨ.choose_spec] with y hy
    exact finsum_nonneg fun w => finsum_nonneg fun _ => hy w
  · exact le_rfl

end Mass

def StatementZero : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (a : ℝ),
    IsIntersectionSystem II → degMu X.H = 0 →
    4 * D.f + 2 ≤ B → ArLimExists X.H X.S B → StokesLimit.Hyp X B a → 0 ≤ arLim X.H X.S B

def StokesLimitMass : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
  ∀ (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D)
    (O abelian₂ : Type) [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂] (Cd : CuspData D O abelian₂)
    (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine H)) (S' : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorr H Cd)),
    Ties H Cd S S' → CuspWeightDefined Cd →
    PtsIntegrable (e := D.n) (mCoordIdeal D.y) (fun _ => phMu H) (fun _ => 1) →
    PtsIntegrable (e := D.n) (mCoordIdeal D.y) (fun _ => phMu H) Cd.cuspWeight →
    ∀ (B : ℕ) (a : ℝ), 4 * D.f + 2 ≤ B → SmoothAtSmallScale H Cd S S' B → ArLimExists H S B →
      RegBound H Cd S' B a → ((D.n : ℝ) + 1) * (a * degMu H -
        ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu H) Cd.cuspWeight / 2) ≤ arLim H S B

end GlobalTheory.CompanionTheory.StokesCompare
