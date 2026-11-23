import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjShiftedEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_proj_shifted_embedding : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : MirabolicParabolic k (i + 1) t), ∃ η : HPG k (i + 1) (t + 1), (η : Mir k ((i + 1) + t + 1)) = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) ∧ pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1, (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.sEmb_HGP_mem_HPG | exact GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.sEmb_HGP_mem_HPG | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.sEmb_HGP_mem_HPG <;> assumption)
