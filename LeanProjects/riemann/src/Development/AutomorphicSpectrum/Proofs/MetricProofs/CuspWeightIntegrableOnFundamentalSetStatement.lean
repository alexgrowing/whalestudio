import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightIntegrableOnFundamentalSet
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_weight_integrable_on_fundamental_set : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (H : Host E) (F : UnivFam E Ψ j j' n g Λ) (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)), F.IsArith Γ → F.IsFundSet Γ FF → 1 ≤ j' → 3 * j' + 1 ≤ j + j' → IntegrableOn (ballDens F.q) FF ∧ 0 < ∫ t in FF, ballDens F.q t ∧ IntegrableOn (fun t => (F.R t).cuspW F.σ * ballDens F.q t) FF ∧ ∫ t in FF, (F.R t).cuspW F.σ * ballDens F.q t ≤ Fintype.card Ψ * j' * (6 + Real.log (2 * Fintype.card Ψ * hostRd E) + Real.log (2 * Fintype.card Ψ * j' * hostRd E)) * ∫ t in FF, ballDens F.q t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.fund_set_mean_cuspW | exact GlobalTheory.CompanionTheory.Ar.Cusp.fund_set_mean_cuspW | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.fund_set_mean_cuspW <;> assumption)
