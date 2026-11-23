import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicPeriodFamily
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_holomorphic_period_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g n : ℕ) (ty : Fin g → (E →+* ℂ)) (V : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g D.La), IsTypeFn H D.p D.q ty → IsOpen V → IsHolFam V R → (∀ t ∈ V, (R t).form = D.EF ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp (R t).B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.p else D.q) → ∀ t₀ ∈ V, ∃ (V' : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → (D.La →+ (Fin g → ℂ))) (h : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen V' ∧ t₀ ∈ V' ∧ V' ⊆ V ∧ IsHolPeriods D ty V' P ∧ (∀ a b, DifferentiableOn ℂ (fun t => h t a b) V') ∧ ∀ t ∈ V', IsUnit (h t).det ∧ ∀ x, P t x = h t *ᵥ (R t).P x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.period_of_riem | exact GlobalTheory.CompanionTheory.Ar.Cusp.period_of_riem | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.period_of_riem <;> assumption)
