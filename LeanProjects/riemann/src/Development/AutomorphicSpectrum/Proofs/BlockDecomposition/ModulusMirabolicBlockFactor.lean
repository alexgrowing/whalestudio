import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

theorem dpowM_hgp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : ℝ) (h : MirabolicParabolic k (i + 1) t), dpowM ((i + 1) + t) s (h : Mir k ((i + 1) + t)) = dpow (i + 1) s (gpProj k (i + 1) t h).1 * dpow (t + 1) s (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) := by
  intro k _ _ _ _ i t s h
  have key : ∀ (n : ℕ) (g : GL (Fin n) k),
      GlobalTheory.BZMir.Leib.dpow n s g = GlobalTheory.SmGL.absPow k (s : ℂ) (Matrix.GeneralLinearGroup.det g) :=
    fun _ _ => rfl
  have hdet : Matrix.GeneralLinearGroup.det
      ((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) =
      Matrix.GeneralLinearGroup.det (GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).1 *
        Matrix.GeneralLinearGroup.det
          (((GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).2 : GlobalTheory.BZMir.Mir k t) :
            GL (Fin (t + 1)) k) := by
    have hp := GlobalTheory.SmGL.det_parab k (GlobalTheory.BZMir.Leib.eGP (i + 1) t)
      (GlobalTheory.BZMir.Leib.hgpIncl k (i + 1) t h)
    rw [Fintype.prod_bool] at hp
    exact hp.trans (mul_comm _ _)
  rw [show GlobalTheory.RgGu.Leib.dpowM ((i + 1) + t) s (h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) =
      GlobalTheory.BZMir.Leib.dpow ((i + 1) + t + 1) s
        ((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) from rfl,
    key, key, key, hdet, map_mul]

end GlobalTheory.CompanionTheory.BZPhiPG

end
