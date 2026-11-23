import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackOfSurjectiveToPushforward
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sectionPullback_of_surjective_toPushforward : ∀ (X T : Scheme.{0}) (i : T ⟶ X) (M : LB X), M.IsLB → Function.Surjective ((GlobalTheory.LB.toPushforward M i).app ⊤) → ∀ σ : (M.pull i).Sec, ∃ u : M.Sec, GlobalTheory.secPull u i = σ := by
  first | exact @GlobalTheory.LB.exists_secPull_eq_of_surjective_toPushforward | exact GlobalTheory.LB.exists_secPull_eq_of_surjective_toPushforward | (intros; apply GlobalTheory.LB.exists_secPull_eq_of_surjective_toPushforward <;> assumption)
