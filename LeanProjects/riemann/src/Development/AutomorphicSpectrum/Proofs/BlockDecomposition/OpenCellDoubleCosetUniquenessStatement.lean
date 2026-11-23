import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellDoubleCosetUniqueness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cell_double_coset_uniqueness : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (r : Mir k ((i + 1) + t)) (d d' : Fin (t + 1) → k), ∀ h ∈ HPG k (i + 1) (t + 1),
  dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) r = h * dEmb k i t d' * wEl k i t →
  ∃ h' ∈ HPG k i (t + 1), castM k (by omega) h' = r := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Stab.mem_of_double_coset | exact GlobalTheory.CompanionTheory.BZPhiPG.Stab.mem_of_double_coset | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Stab.mem_of_double_coset <;> assumption)
