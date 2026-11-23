import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFreeModuleCompactAdicDvr
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_free_module_compact_adic_dvr : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul O M] [T2Space M] [Module.Free O M] [Module.Finite O M] (ϖ : O), Irreducible ϖ → CompactSpace M ∧ IsOpen (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) ∧ Topology.IsClosedEmbedding (fun m : M => ϖ • m) := by
  first | exact @GlobalTheory.finite_free_compact_adic_dvr | exact GlobalTheory.finite_free_compact_adic_dvr | (intros; apply GlobalTheory.finite_free_compact_adic_dvr <;> assumption)
