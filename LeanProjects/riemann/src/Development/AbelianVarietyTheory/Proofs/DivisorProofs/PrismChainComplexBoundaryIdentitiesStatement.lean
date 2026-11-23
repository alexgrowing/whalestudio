import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrismChainComplexBoundaryIdentities
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prism_chain_complex_boundary_identities : (∀ N (c : Pr N →₀ ℤ), Pr.d N (Pr.d N c) = 0) ∧ (∀ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) c, Pr.d M (Pr.push θ c) = Pr.push θ (Pr.d N c)) ∧ (∀ N k (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.Deg k (Pr.d N c)) ∧ (∀ N k (c : Pr N →₀ ℤ), Pr.Deg k c → Pr.Deg k (Pr.bd c)) ∧ (∀ N (c : Pr N →₀ ℤ), Pr.bd (Pr.bd c) = 0) ∧ (∀ N (c : Pr N →₀ ℤ), Pr.d (N + 1) (Pr.bd c) = Pr.bd (Pr.d N c)) ∧ ∀ N, Pr.Deg N (Pr.aw N) ∧ Pr.Deg N (Pr.wa N) := by
  first | (exact @GlobalTheory.EtC.PrCx.pr_complex) | (exact GlobalTheory.EtC.PrCx.pr_complex) | (intros; apply GlobalTheory.EtC.PrCx.pr_complex  <;> assumption)
