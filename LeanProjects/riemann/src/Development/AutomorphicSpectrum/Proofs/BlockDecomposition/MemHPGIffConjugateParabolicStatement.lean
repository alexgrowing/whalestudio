import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHPGIffConjugateParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_HPG_iff_conjugate_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ} (h : (i + 1) + t = i + t + 1) (p : Mir k (i + t)), p ∈ HPG k i t ↔ wGL k h * (p : GL (Fin (i + t + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h)) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.mem_HPG_iff_conj_mem_parab | exact GlobalTheory.CompanionTheory.BZRes.mem_HPG_iff_conj_mem_parab | (intros; apply GlobalTheory.CompanionTheory.BZRes.mem_HPG_iff_conj_mem_parab <;> assumption)
