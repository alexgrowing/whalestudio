import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ThetaArchimedeanDataDefiniteModelsNonempty
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaArchimedeanData_definiteModels_nonempty : ∀ (D : D7) (T : Top D) (h : LawsP T) (EX : ErrX D) (p : ℕ) (hj : InR D D.R.m) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D D.R.m) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ), ParOK T EX p D.R.m → PageOK large₂ (recPJ h D.R.m hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h D.R.m hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → ∀ (N : ℕ) (w : Fin N → (recB h.toLawsCore).Cusp D.R.m wL), NoCommonZero (T.Q.Xo D.R.m) T.Q.c (fun i => (w i).1) → Nonempty (GlobalTheory.Shares.ArchAt h D.R.m w wF Tn 1) := by
  first | exact @GlobalTheory.ArchDefinite.archAt_nonempty_of_definite | exact GlobalTheory.ArchDefinite.archAt_nonempty_of_definite | (intros; apply GlobalTheory.ArchDefinite.archAt_nonempty_of_definite <;> assumption)
