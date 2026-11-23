import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexScaledMaxIdeal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
open ValuativeRel GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_inf_mul_relIndex_inf_eq_resCard_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (c : ℤ) (L P : AddSubgroup k), (∀ x, x ∈ L ↔ valuation k x < 1) → (∀ x, x ∈ P ↔ valuation k (((ϖ ^ c : kˣ) : k) * x) < 1) → (P ⊓ L).relIndex P * (P ⊓ L).relIndex L = resCard k ^ c.natAbs := by
  first | exact @GlobalTheory.ScaledIdealIndex.relIndex_scaled_maxIdeal | exact GlobalTheory.ScaledIdealIndex.relIndex_scaled_maxIdeal | (intros; apply GlobalTheory.ScaledIdealIndex.relIndex_scaled_maxIdeal <;> assumption)
