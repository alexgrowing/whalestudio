import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistedKernel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSupport
open GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_induction_twisted_kernel : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (H U : Subgroup G) [U.Normal], U ≤ H → (∀ O : Set G, O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) → ∀ (σ : Representation ℂ H W), IsSmooth σ → ∀ f : cIndSpace H σ, (∀ g, f.1.1.1 g ∈ twKer σ (U.subgroupOf H) 1) → f ∈ twKer (cInd H σ) U 1 := by
  first | exact @GlobalTheory.CompanionTheory.PRep.CIndKer.mem_twKer_cInd | exact GlobalTheory.CompanionTheory.PRep.CIndKer.mem_twKer_cInd | (intros; apply GlobalTheory.CompanionTheory.PRep.CIndKer.mem_twKer_cInd <;> assumption)
