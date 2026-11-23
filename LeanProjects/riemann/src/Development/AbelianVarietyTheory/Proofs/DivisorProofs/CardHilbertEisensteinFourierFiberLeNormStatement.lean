import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardHilbertEisensteinFourierFiberLeNorm
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hilbertEisensteinFourierFiber_le_norm : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (ξ : F) (s : Finset (Quotient (qRel 𝔞 𝔟))), (∀ c ∈ s, c.out.1.1 * c.out.1.2 = ξ) → (s.card : ℝ) ≤ |(Algebra.norm ℚ ξ : ℝ)| / (nrm 𝔞 * nrm 𝔟) := by
  first | exact @GlobalTheory.QFiber.card_le_norm | exact GlobalTheory.QFiber.card_le_norm | (intros; apply GlobalTheory.QFiber.card_le_norm <;> assumption)
