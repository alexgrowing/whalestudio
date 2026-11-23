import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedCellRightStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_cell_right_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), ∀ p ∈ Cl k i t, ∀ m, p * sO k i t m ∈ Cl k i t := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO <;> assumption)
