import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightUniformOnCompact
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoC2Statement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularChartDataPropertiesStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_weight_uniform_on_compact : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B), S.IsTied → ∀ K' ⊆ S.R.Yo, IsCompact K' → TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) K' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendstoUniformlyOn_regWeight_of_isCompact_subset_Yo | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendstoUniformlyOn_regWeight_of_isCompact_subset_Yo | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendstoUniformlyOn_regWeight_of_isCompact_subset_Yo <;> assumption)
