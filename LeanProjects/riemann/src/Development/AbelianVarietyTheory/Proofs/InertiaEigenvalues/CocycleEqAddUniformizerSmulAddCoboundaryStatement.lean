import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleEqAddUniformizerSmulAddCoboundary
import Mathlib
import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_eq_add_uniformizer_smul_add_coboundary : ∀ {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] {G : Type} [Group G] [TopologicalSpace G] (ρ : Representation O G M), ContAction ρ → ∀ (ϖ : O), Topology.IsEmbedding (fun m : M => ϖ • m) → ∀ (s : Finset (Z1 ρ)), (∀ c : Z1 ρ, ∃ i ∈ s, ∃ x : M, ∀ g, (c : G → M) g - (i : G → M) g - (ρ g x - x) ∈ LinearMap.range (LinearMap.lsmul O M ϖ)) → ∀ c : Z1 ρ, ∃ (a : Z1 ρ → O) (c' : Z1 ρ) (x : M), (c : G → M) = ∑ i ∈ s, a i • (i : G → M) + ϖ • (c' : G → M) + d0 ρ x := by
  first | exact @GlobalTheory.cocycle_lift_mod_uniformizer | exact GlobalTheory.cocycle_lift_mod_uniformizer | (intros; apply GlobalTheory.cocycle_lift_mod_uniformizer <;> assumption)
