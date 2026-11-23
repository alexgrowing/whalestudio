import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h_zero_pullback_twist_bijective : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A'), IsUnit (q : A) → (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → Nontrivial A' → (∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) → (∀ e : A', IsIdempotentElem e → e = 0 ∨ e = 1) → ∀ i : ℤ, Function.Bijective (pull _ (spMap f) (tw q i) 0) := by
  first | (exact @GlobalTheory.EtC.h_zero_pull_bijective) | (exact GlobalTheory.EtC.h_zero_pull_bijective) | (intros; apply GlobalTheory.EtC.h_zero_pull_bijective  <;> assumption)
