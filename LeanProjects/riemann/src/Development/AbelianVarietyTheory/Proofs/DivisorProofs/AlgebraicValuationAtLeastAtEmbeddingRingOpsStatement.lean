import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastAtEmbeddingRingOps
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), (∀ r : ℝ, Sz l lam r 0) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r y → Sz l lam r (x + y) ∧ Sz l lam r (x - y)) ∧ (∀ (r s : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam s y → Sz l lam (r + s) (x * y)) ∧ (∀ (r s : ℝ) (x : ℂ), r ≤ s → Sz l lam r x → Sz l lam s x) ∧ (∀ n : ℤ, Sz l lam 0 (n : ℂ)) ∧ (∀ (κ : Type) (t : Finset κ) (r : ℝ) (x : κ → ℂ), (∀ k ∈ t, Sz l lam r (x k)) → Sz l lam r (∑ k ∈ t, x k)) := by
  first | exact @GlobalTheory.QFam.SzSum.sz_ring | exact GlobalTheory.QFam.SzSum.sz_ring | (intros; apply GlobalTheory.QFam.SzSum.sz_ring <;> assumption)
