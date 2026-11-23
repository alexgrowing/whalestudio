import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.RemovableLogGrowthSingularity
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_sum_tensor_product : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', boxFun φ₁ φ₂ ∈ schA F (κ ⊕ κ') ∧ thetaSum F (boxFun φ₁ φ₂) = thetaSum F φ₁ * thetaSum F φ₂ := by
  first | exact @GlobalTheory.CompanionTheory.ThetaBox.theta_box | exact GlobalTheory.CompanionTheory.ThetaBox.theta_box | (intros; apply GlobalTheory.CompanionTheory.ThetaBox.theta_box <;> assumption)
