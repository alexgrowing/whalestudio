import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLagrangeResolventOfPGroupFaithful
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lagrange_resolvent_of_pGroup_faithful : ∀ (L : Type) [Field L] (p : ℕ), p.Prime → ∀ (G : Type) [Group G] [MulSemiringAction G L] [Finite G] [Nontrivial G] [FaithfulSMul G L], IsPGroup p G → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ∃ (σ : G) (α : L), α ≠ 0 ∧ σ • α = ζ * α ∧ ∀ g : G, g • α ^ p = α ^ p := by
  first | exact @GlobalTheory.AlmostEt.exists_lagrange_resolvent | exact GlobalTheory.AlmostEt.exists_lagrange_resolvent | (intros; apply GlobalTheory.AlmostEt.exists_lagrange_resolvent <;> assumption)
