import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AevalNegEqZeroOfResolventIdentity
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_neg_eq_zero_of_resolvent_identity : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (p : Polynomial ℂ), (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = p.eval u • w) → Polynomial.aeval (-Ω) p = 0 ∧ ∀ (α : ℂ) (w : N), Ω w = α • w → ∀ (q : Polynomial ℂ), p = (Polynomial.X + Polynomial.C α) * q → ∀ u : ℂ, X u w = q.eval u • w := by
  first | exact @GlobalTheory.aeval_neg_eq_zero_and_eigen_of_resolvent_identity | exact GlobalTheory.aeval_neg_eq_zero_and_eigen_of_resolvent_identity | (intros; apply GlobalTheory.aeval_neg_eq_zero_and_eigen_of_resolvent_identity <;> assumption)
