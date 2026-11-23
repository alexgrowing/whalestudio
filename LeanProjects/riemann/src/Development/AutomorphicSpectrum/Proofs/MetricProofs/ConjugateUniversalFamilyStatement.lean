import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateUniversalFamily
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_universal_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ), ∃ F' : UnivFam E Ψ j j' n g Λ, F'.q = F.q ∧ (∀ τ, F'.σ τ = (starRingEnd ℂ).comp (F.σ τ)) ∧ F'.form = -F.form ∧ ∀ t, (∀ x, (F'.R t).P x = star ((F.R (star t)).P x)) ∧ (F'.R t).Hm = (F.R (star t)).Hm.map (starRingEnd ℂ) ∧ ∀ a x, (F'.R t).B a x = star ((F.R (star t)).B a (star x)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.exists_conj_univFam | exact GlobalTheory.CompanionTheory.Ar.Cusp.exists_conj_univFam | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.exists_conj_univFam <;> assumption)
