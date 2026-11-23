import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousShiftedOrbitMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_shifted_orbit_map : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), Continuous (sO k i t) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.continuous_sO | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.continuous_sO | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.continuous_sO <;> assumption)
