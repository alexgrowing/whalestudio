import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionClosedCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_section_closed_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ} (h : (i + 1) + t = i + t + 1), 0 < t → LocSec (parab k (two (stdSum h))) (Mir k (i + t)) 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.locSec_parab_mir_one | exact GlobalTheory.CompanionTheory.BZRes.locSec_parab_mir_one | (intros; apply GlobalTheory.CompanionTheory.BZRes.locSec_parab_mir_one <;> assumption)
