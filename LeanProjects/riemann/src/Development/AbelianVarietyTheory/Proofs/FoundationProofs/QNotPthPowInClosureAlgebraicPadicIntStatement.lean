import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QNotPthPowInClosureAlgebraicPadicInt
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.q_not_pth_pow_in_closure_algebraic_padicInt : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}),
      b ^ p ≠ algebraMap (O0 p) Ω (qO p) := by
  first | exact @GlobalTheory.K5.NotPow.q_not_pow | exact GlobalTheory.K5.NotPow.q_not_pow | (intros; apply GlobalTheory.K5.NotPow.q_not_pow <;> assumption)
