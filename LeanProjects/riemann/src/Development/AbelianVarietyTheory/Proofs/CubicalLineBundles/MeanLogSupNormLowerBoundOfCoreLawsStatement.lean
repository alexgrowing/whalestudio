import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundOfCoreLaws
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcWitnessExistence.DataXOfModel
import Formalism.LocalToGlobal.ProjectiveLattices.ExtendedPointBaseChange
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLam
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanLogSupNorm_lower_bound_of_coreLaws : ∃ C0 : ℝ, 0 < C0 ∧ ∀ (D : D7) (T : Core D) (h : LawsCore T), GamAt T → ∀ (large₂ : SizeData₂ D), (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) → ∀ (j : ℕ) (w : WeightFamilies.Wt D j) (C A : ℝ), C0 ≤ C → 2 ≤ A → Formalism.MainNotions.Gaps.EtaleWeightGaps.LAMwAt large₂ (recB h) j w C A := by
  first | exact @GlobalTheory.lamwAt_of_lawsCore | exact GlobalTheory.lamwAt_of_lawsCore | (intros; apply GlobalTheory.lamwAt_of_lawsCore <;> assumption)
