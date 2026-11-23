import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenDoubleCosetCriterion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_double_coset_criterion : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ} (h : (i + 1) + t = i + t + 1), 0 < t → ∀ g : GL (Fin (i + t + 1)) k, g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) ↔ ∃ a : Fin (i + 1), ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) (stdSum h (Sum.inl a)) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.mem_dcos_wGL_iff | exact GlobalTheory.CompanionTheory.BZRes.mem_dcos_wGL_iff | (intros; apply GlobalTheory.CompanionTheory.BZRes.mem_dcos_wGL_iff <;> assumption)
