import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueCocycle
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_cocycle_alt : ∀ (l : ℕ) [Fact l.Prime] (G M : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [T2Space M] (a : G → (M →+ M)), (∀ x, a 1 x = x) → (∀ g h x, a (g * h) x = a g (a h x)) → Continuous (fun p : G × M => a p.1 p.2) → ∀ T : AddSubgroup M, IsCompact (T : Set M) → (∀ g, ∀ t ∈ T, a g t ∈ T) → (∀ U ∈ nhds (0 : M), ∃ k : ℕ, ∀ t ∈ T, l ^ k • t ∈ U) → ∀ (lam : G →* Multiplicative ℤ_[l]) (g₀ : G), Continuous lam → lam g₀ = Multiplicative.ofAdd 1 → ∀ b z : M, (∀ h, lam h = 1 → a h z = z ∧ a h b - b ∈ T) → z - (a g₀ b - b) ∈ T → ∃! c : G → M, Continuous c ∧ (∀ g, c g ∈ T) ∧ (∀ g h, c (g * h) = c g + a g (c h)) ∧ (∀ h, lam h = 1 → c h = -(a h b - b)) ∧ ∀ g, lam g = Multiplicative.ofAdd 1 → c g = z - (a g b - b) := by
  first | exact @GlobalTheory.HlCoc.exists_unique_cocycle | exact GlobalTheory.HlCoc.exists_unique_cocycle | (intros; apply GlobalTheory.HlCoc.exists_unique_cocycle <;> assumption)
