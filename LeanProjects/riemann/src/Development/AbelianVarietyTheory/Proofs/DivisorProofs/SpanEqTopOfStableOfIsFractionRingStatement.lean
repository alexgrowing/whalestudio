import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopOfStableOfIsFractionRing
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_eq_top_of_stable_of_isFractionRing' : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k K] [Algebra F K] [FiniteDimensional F K] (B : Subalgebra k K) [IsFractionRing B K] (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Submodule.span K S = ⊤ → Submodule.span F S = ⊤ := by
  first | (exact @GlobalTheory.span_eq_top_of_stable_of_isFractionRing) | (exact GlobalTheory.span_eq_top_of_stable_of_isFractionRing) | (intros; apply GlobalTheory.span_eq_top_of_stable_of_isFractionRing  <;> assumption)
