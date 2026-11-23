import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondDerivativeHolomorphicSymm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.second_derivative_holomorphic_symm : ∀ {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E'] (φ : E' → E) (b v w : E'), (∀ᶠ c in 𝓝 b, DifferentiableAt ℂ φ c) → fderiv ℂ (fun c => fderiv ℂ φ c v) b w = fderiv ℂ (fun c => fderiv ℂ φ c w) b v := by
  first | exact @GlobalTheory.fderiv_fderiv_apply_symm_of_eventually_differentiableAt | exact GlobalTheory.fderiv_fderiv_apply_symm_of_eventually_differentiableAt | (intros; apply GlobalTheory.fderiv_fderiv_apply_symm_of_eventually_differentiableAt <;> assumption)
