import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupAverageComponentwiseSubgroupEqProd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
open Filter GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupAverage_componentwiseSubgroup_eq_prod : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (K : Subgroup G) (KH : ∀ i, Subgroup (H i)) (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) (u : ∀ i, KH i → ℂ), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ i, (rStab (u i)).index ≠ 0) → (∀ᶠ i in cofinite, ∀ k, u i k = 1) → avg (fun k : K => ∏ᶠ i, u i ⟨p i k, (hK k).1 k.2 i⟩) = ∏ᶠ i, avg (u i) := by
  first | exact @GlobalTheory.AvgRestr.avg_restrProd | exact GlobalTheory.AvgRestr.avg_restrProd | (intros; apply GlobalTheory.AvgRestr.avg_restrProd <;> assumption)
