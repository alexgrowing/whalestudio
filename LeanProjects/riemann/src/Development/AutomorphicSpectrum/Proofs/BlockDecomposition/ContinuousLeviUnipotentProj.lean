import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPsiMinus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirProj
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.Cont

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colMat_entry (n : ℕ) (a b : Fin (n + 1)) :
    Continuous fun y : Fin n → k => colMat k n y a b := by
  unfold colMat
  split_ifs
  · induction a using Fin.lastCases with
    | last => simp only [Fin.lastCases_last]; exact continuous_const
    | cast i => simp only [Fin.lastCases_castSucc]; exact continuous_apply i
  · exact continuous_const

theorem continuous_uM_val (n : ℕ) : Continuous fun y : Fin n → k =>
    (((uM k n y : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
  have h : (fun y : Fin n → k =>
      (((uM k n y : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) =
      fun y => 1 + colMat k n y := by
    funext y
    rfl
  rw [h]
  refine continuous_const.add (continuous_matrix fun a b => ?_)
  exact continuous_colMat_entry k n a b

theorem uM_inv (n : ℕ) (y : Fin n → k) : (uM k n y)⁻¹ = uM k n (-y) := by
  have h : uM k n (-y) * uM k n y = 1 := by
    rw [← uM_add, neg_add_cancel, uM_zero]
  exact (eq_inv_of_mul_eq_one_left h).symm

theorem continuous_uM (n : ℕ) : Continuous (uM k n) := by
  apply continuous_induced_rng.2
  refine Units.continuous_iff.2 ⟨continuous_uM_val k n, ?_⟩
  have h : ∀ y : Fin n → k, ((uM k n y : GL (Fin (n + 1)) k))⁻¹ =
      (uM k n (-y) : GL (Fin (n + 1)) k) := by
    intro y
    rw [← uM_inv k n y, Subgroup.coe_inv]
  simp only [Function.comp_apply, h]
  exact (continuous_uM_val k n).comp continuous_neg

end GlobalTheory.CompanionTheory.BZPsiPG.Cont

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem continuous_levi_uM_mirProj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (levi k n) ∧ Continuous (uM k n) ∧ Continuous (mirabolicProjection k n) := by
  intro k _ _ _ _ n
  exact ⟨GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k n, Cont.continuous_uM k n,
    GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k n⟩

end GlobalTheory.CompanionTheory.BZPsiPG
