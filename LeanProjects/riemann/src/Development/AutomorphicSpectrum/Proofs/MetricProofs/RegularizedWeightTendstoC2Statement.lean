import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoC2
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_weight_tendsto_C2 : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B), S.IsTied → ∀ j, ∀ K' ⊆ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => S.regWeight t ∘ (M.atlas.chart j).symm) (S.R.ph ∘ (M.atlas.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (S.regWeight t ∘ (M.atlas.chart j).symm)) (fderiv ℝ (S.R.ph ∘ (M.atlas.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (S.regWeight t ∘ (M.atlas.chart j).symm))) (fderiv ℝ (fderiv ℝ (S.R.ph ∘ (M.atlas.chart j).symm))) (𝓝[>] 0) K' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.regWeight_tendsto_C2_of_tied | exact GlobalTheory.CompanionTheory.Ar.Giv.regWeight_tendsto_C2_of_tied | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.regWeight_tendsto_C2_of_tied <;> assumption)
