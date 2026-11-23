import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationExtendPadicLaurentToClosure
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_extend_padicLaurent_to_closure : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ D : Derivation ℤ (O0 p) (O0 p),
    ∃ E : Derivation ℤ Ω Ω, ∀ x, E (algebraMap (O0 p) Ω x) = algebraMap (O0 p) Ω (D x) := by
  first | exact @GlobalTheory.K5.DerExt.derivation_extend | exact GlobalTheory.K5.DerExt.derivation_extend | (intros; apply GlobalTheory.K5.DerExt.derivation_extend <;> assumption)
