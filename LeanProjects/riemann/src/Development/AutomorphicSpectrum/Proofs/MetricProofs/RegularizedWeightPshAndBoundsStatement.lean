import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightPshAndBounds
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_weight_psh_and_bounds : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B) (Θ : LocPot M.Xc), S.IsTied → IsPotential M.atlas Θ → IsPosPot M.atlas Θ → ReciprocityTheory.AnForm.P.IsPshOn M.atlas S.R.Yo (S.R.th + LocPot.ofFun S.R.ph) ∧ (∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) ∧ ∀ x ∈ S.R.Yo, S.R.ph x ≤ S.regWeight t x ∧ S.regWeight t x ≤ C) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), IsPsh M.atlas (S.R.th + LocPot.ofFun (S.regWeight t) + Θ.rsmul ε) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.tied_regularisation_weak | exact GlobalTheory.CompanionTheory.Ar.Giv.tied_regularisation_weak | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.tied_regularisation_weak <;> assumption)
