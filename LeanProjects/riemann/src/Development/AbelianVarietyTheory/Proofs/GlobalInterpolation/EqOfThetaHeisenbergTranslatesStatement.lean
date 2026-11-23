import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfThetaHeisenbergTranslates
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_theta_heisenbergTranslates : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ G G' : (Fin N → AF F) → ℂ, Decay G → Decay G' → (∀ x y, th (rho ψ a x y G) = th (rho ψ a x y G')) → G = G' := by
  first | exact @GlobalTheory.SWQ.eq_of_theta_rho | exact GlobalTheory.SWQ.eq_of_theta_rho | (intros; apply GlobalTheory.SWQ.eq_of_theta_rho <;> assumption)
