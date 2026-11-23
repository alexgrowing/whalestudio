import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermSmulAddDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeriesTerm_smul_add_decomposition : ∀ (O : Type) [CommRing O] (N : GlobalTheory.Ex.NumD O) (S : Subring O) (m : ℕ) (h : N.Gt) (y : N.X), h ^ m = N.io y → (∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), ∀ x' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), ∀ x'' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), (N.θ x x' x'' : O) ∈ S ∧ (((N.θ x x' x'')⁻¹ : Oˣ) : O) ∈ S) → (∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), (N.σ x : O) ∈ S ∧ (((N.σ x)⁻¹ : Oˣ) : O) ∈ S) → ∀ a b : N.X, ∃ w : Oˣ, (w : O) ∈ S ∧ N.ψ (m • a + b) * h.s (m • a + b) = w * N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b) := by
  first | exact @GlobalTheory.theta_term_smul_add | exact GlobalTheory.theta_term_smul_add | (intros; apply GlobalTheory.theta_term_smul_add <;> assumption)
