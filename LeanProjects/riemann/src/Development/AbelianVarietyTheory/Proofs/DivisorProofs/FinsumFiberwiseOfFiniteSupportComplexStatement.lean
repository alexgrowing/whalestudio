import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumFiberwiseOfFiniteSupportComplex
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_fiberwise_of_finite_support_complex : ∀ {A B : Type} (ρ : A → B) (f : A → ℂ), (Function.support f).Finite → ∑ᶠ a, f a = ∑ᶠ b, ∑ᶠ a : {a // ρ a = b}, f a.1 := by
  first | exact @GlobalTheory.finsum_fiberwise_of_finite_support | exact GlobalTheory.finsum_fiberwise_of_finite_support | (intros; apply GlobalTheory.finsum_fiberwise_of_finite_support <;> assumption)
