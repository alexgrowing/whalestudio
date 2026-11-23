import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingMemLevi
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_embedding_mem_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (g : Levi k (fun a => Fin (d a))), leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd) := by
  first | exact @GlobalTheory.CompanionTheory.LeviBlockIdx.leviEmb_mem_levi_blockIdx | exact GlobalTheory.CompanionTheory.LeviBlockIdx.leviEmb_mem_levi_blockIdx | (intros; apply GlobalTheory.CompanionTheory.LeviBlockIdx.leviEmb_mem_levi_blockIdx <;> assumption)
