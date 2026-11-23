import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFundamentalSet
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamental_set : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (Δ : GroupDict F) (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)), F.IsArith Γ → ∃ FF, F.IsFundSet Γ FF := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.exists_isFundSet | exact GlobalTheory.CompanionTheory.Ar.Cusp.exists_isFundSet | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.exists_isFundSet <;> assumption)
