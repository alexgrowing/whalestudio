import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsElementAngleNontrivial
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_element_angle_nontrivial : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : E →+* ℂ) (κ : ℕ), 0 < κ → ∃ ξ : E, ξ ≠ 0 ∧ (τ ξ / (‖τ ξ‖ : ℂ)) ^ κ ≠ 1 := by
  first | exact @GlobalTheory.CMArg.exists_ne_zero_arg_pow_ne_one | exact GlobalTheory.CMArg.exists_ne_zero_arg_pow_ne_one | (intros; apply GlobalTheory.CMArg.exists_ne_zero_arg_pow_ne_one <;> assumption)
