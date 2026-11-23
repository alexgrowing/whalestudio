import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteLevelApproxOfGeometricInvariantModPo
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteLevel_approx_of_geometric_invariant_modPow : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ x : Ω, IsInt p x →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong p k (g x) x) →
  ∃ y : Ω, IsInt p y ∧ (∃ N, ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) ∧
    Cong p k ((T.ζ j - 1) * x) y := by
  first | exact @GlobalTheory.K5.geo_invariants_from_finite_level | exact GlobalTheory.K5.geo_invariants_from_finite_level | (intros; apply GlobalTheory.K5.geo_invariants_from_finite_level <;> assumption)
