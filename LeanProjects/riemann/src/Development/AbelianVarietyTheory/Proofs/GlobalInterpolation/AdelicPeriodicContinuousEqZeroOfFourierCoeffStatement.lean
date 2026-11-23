import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicPeriodicContinuousEqZeroOfFourierCoeff
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPeriodic_continuous_eq_zero_of_fourier_coeff : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ D : Set (Fin N → AF F), IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) → muV N ν D = 1 → ∀ P : (Fin N → AF F) → ℂ, Continuous P → (∀ ξ u, P (rat ξ + u) = P u) → (∀ ξ : Fin N → F, ∫ u in D, P u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = 0) → P = 0 := by
  first | exact @GlobalTheory.SWQ.periodic_eq_zero_of_coeff | exact GlobalTheory.SWQ.periodic_eq_zero_of_coeff | (intros; apply GlobalTheory.SWQ.periodic_eq_zero_of_coeff <;> assumption)
