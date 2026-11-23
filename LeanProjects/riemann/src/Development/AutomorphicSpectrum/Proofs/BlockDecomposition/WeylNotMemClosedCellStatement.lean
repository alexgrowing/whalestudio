import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylNotMemClosedCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_not_mem_closed_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), wEl k i t ∉ Cl k i t ∧ dEmb k i t 0 = 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.wEl_notMem_Cl_and_dEmb_zero | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.wEl_notMem_Cl_and_dEmb_zero | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.wEl_notMem_Cl_and_dEmb_zero <;> assumption)
