import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicFourierSeriesOfSummableCoefficients
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_fourierSeries_of_summable_coefficients : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ D : Set (Fin N → AF F), IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) → muV N ν D = 1 → ∀ (P : (Fin N → AF F) → ℂ) (c : (Fin N → F) → ℂ), Continuous P → (∀ ξ u, P (rat ξ + u) = P u) → (∀ ξ, ∫ u in D, P u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = c ξ) → Summable (fun ξ => ‖c ξ‖) → ∀ u, P u = ∑' ξ, c ξ * ψ (Bd (AF F) a u (rat ξ)) := by
  first | exact @GlobalTheory.SWQ.FourierSeries.fourier_series | exact GlobalTheory.SWQ.FourierSeries.fourier_series | (intros; apply GlobalTheory.SWQ.FourierSeries.fourier_series <;> assumption)
