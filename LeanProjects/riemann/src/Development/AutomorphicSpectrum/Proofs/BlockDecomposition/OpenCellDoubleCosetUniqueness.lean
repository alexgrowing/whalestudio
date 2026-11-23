import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCellStructureData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Stab

section Perm

theorem piPerm_true_val (i t : ℕ) (x : Fin (t + 1)) (hx : i + x.val < (i + 1) + t + 1) :
    (piPerm i t ⟨i + x.val, hx⟩).val = i + 1 + x.val := by
  have h : (finCongr (by omega : i + 1 + t + 1 = i + (t + 1) + 1) ⟨i + x.val, hx⟩ :
      Fin (i + (t + 1) + 1)) = GlobalTheory.BZMir.Leib.ePG i (t + 1) ⟨true, x⟩ :=
    Fin.ext (by simp [GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val])
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.piPerm, Equiv.trans_apply]
  rw [h, Equiv.symm_apply_apply, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val]

theorem piPerm_false_val (i t : ℕ) (y : Fin i) (hy : y.val < (i + 1) + t + 1) :
    (piPerm i t ⟨y.val, hy⟩).val = y.val := by
  have h : (finCongr (by omega : i + 1 + t + 1 = i + (t + 1) + 1) ⟨y.val, hy⟩ :
      Fin (i + (t + 1) + 1)) = GlobalTheory.BZMir.Leib.ePG i (t + 1) ⟨false, Fin.castSucc y⟩ :=
    Fin.ext (by simp [GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_false_val])
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.piPerm, Equiv.trans_apply]
  rw [h, Equiv.symm_apply_apply, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val]
  all_goals simp

end Perm

section Ent

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem castM_symm_entry {a b : ℕ} (e : a = b) (r : Mir k b) (x y : ℕ) (hx : x < a + 1) (hy : y < a + 1)
    (hx' : x < b + 1) (hy' : y < b + 1) :
    (((castM k e).symm r : Mir k a) : GL (Fin (a + 1)) k).val ⟨x, hx⟩ ⟨y, hy⟩ =
      (r : GL (Fin (b + 1)) k).val ⟨x, hx'⟩ ⟨y, hy'⟩ := by
  subst e
  rfl

theorem mirProj_dEmb (i t : ℕ) (d : Fin (t + 1) → k) : mirabolicProjection k _ (dEmb k i t d) = 1 := by
  apply GlobalTheory.CompanionTheory.BZPhiPG.Grp.mirProj_eq_one_of_mem
  exact Subgroup.mem_subgroupOf.mpr
    (MonoidHom.mem_range.mpr ⟨_, rfl⟩)

theorem mirProj_wEl (i t : ℕ) : mirabolicProjection k _ (wEl k i t) = wGL k i t :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_levi _ _

theorem mirProj_sEmb (n : ℕ) (r : Mir k n) : mirabolicProjection k _ (sEmb k n r) = (r : GL (Fin (n + 1)) k) :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_levi _ _

theorem wGL_mul_apply (i t : ℕ) (M : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) (a b : Fin ((i + 1) + t + 1)) :
    ((wGL k i t).val * M) (piPerm i t a) b = M a b := by
  show (Equiv.Perm.permMatrix k (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t)⁻¹ * M) (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t a) b = M a b
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply]
  simp

theorem mul_wGL_apply (i t : ℕ) (M : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) (a b : Fin ((i + 1) + t + 1)) :
    (M * (wGL k i t).val) a b = M a (piPerm i t b) := by
  show (M * Equiv.Perm.permMatrix k (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t)⁻¹) a b = M a (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t b)
  rw [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply]
  simp [Equiv.Perm.inv_def]

theorem entry_eq (i t : ℕ) (r : Mir k ((i + 1) + t)) (d d' : Fin (t + 1) → k) (h : Mir k ((i + 1) + t + 1))
    (e : dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) r = h * dEmb k i t d' * wEl k i t)
    (x y : Fin ((i + 1) + t + 1)) :
    (r : GL (Fin ((i + 1) + t + 1)) k).val x y =
      (h : GL (Fin ((i + 1) + t + 1 + 1)) k).val (Fin.castSucc (piPerm i t x)) (Fin.castSucc (piPerm i t y)) := by
  have key := congrArg (GlobalTheory.BZMir.mirabolicProjection k ((i + 1) + t + 1)) e
  simp only [map_mul, GlobalTheory.CompanionTheory.BZPhiPG.Stab.mirProj_dEmb, GlobalTheory.CompanionTheory.BZPhiPG.Stab.mirProj_wEl,
    GlobalTheory.CompanionTheory.BZPhiPG.Stab.mirProj_sEmb, _root_.one_mul, _root_.mul_one] at key
  have key' := congrArg (fun g : GL (Fin ((i + 1) + t + 1)) k =>
    (g : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t x) y) key
  simp only [Units.val_mul, GlobalTheory.CompanionTheory.BZPhiPG.Stab.wGL_mul_apply, GlobalTheory.CompanionTheory.BZPhiPG.Stab.mul_wGL_apply] at key'
  exact key'

theorem entry_zero (i t : ℕ) (r : Mir k ((i + 1) + t)) (d d' : Fin (t + 1) → k) (h : Mir k ((i + 1) + t + 1))
    (hh : h ∈ HPG k (i + 1) (t + 1))
    (e : dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) r = h * dEmb k i t d' * wEl k i t)
    (x y : Fin ((i + 1) + t + 1)) (hx : i < (piPerm i t x).val) (hy : (piPerm i t y).val ≤ i) :
    (r : GL (Fin ((i + 1) + t + 1)) k).val x y = 0 := by
  rw [GlobalTheory.CompanionTheory.BZPhiPG.Stab.entry_eq i t r d d' h e x y]
  have hc : (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t y : ℕ) < i + 1 := by omega
  have hz := GlobalTheory.CompanionTheory.BZPhiPG.Grp.hpg_entry h hh
    (Fin.castSucc (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t x))
    (by rw [Fin.coe_castSucc]; exact hx)
    (by rw [Fin.coe_castSucc]; exact Nat.ne_of_lt (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t x).isLt)
    ⟨(GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t y : ℕ), hc⟩
  have e₂ : (Fin.castLE (by omega) (⟨(GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t y : ℕ), hc⟩ : Fin (i + 1)) :
      Fin ((i + 1) + t + 1 + 1)) = Fin.castSucc (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t y) := Fin.ext rfl
  rw [e₂] at hz
  exact hz

end Ent

theorem mem_of_double_coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (r : Mir k ((i + 1) + t)) (d d' : Fin (t + 1) → k), ∀ h ∈ HPG k (i + 1) (t + 1),
  dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) r = h * dEmb k i t d' * wEl k i t →
  ∃ h' ∈ HPG k i (t + 1), castM k (by omega) h' = r := by
  intro k _ _ _ _ i t r d d' h hh e
  have hab : i + (t + 1) = (i + 1) + t := by omega
  refine ⟨(GlobalTheory.CompanionTheory.BZPhiPG.castM k hab).symm r, ?_, MulEquiv.apply_symm_apply _ _⟩
  apply GlobalTheory.CompanionTheory.BZPhiPG.Cells.mem_HPG_of
  · intro x y
    have hxl := x.isLt
    have hyl := y.isLt
    refine (GlobalTheory.CompanionTheory.BZPhiPG.Stab.castM_symm_entry hab r (i + x.val) y.val (by omega) (by omega)
      (by omega) (by omega)).trans ?_
    exact GlobalTheory.CompanionTheory.BZPhiPG.Stab.entry_zero i t r d d' h hh e _ _
      (by rw [GlobalTheory.CompanionTheory.BZPhiPG.Stab.piPerm_true_val]; omega) (by rw [GlobalTheory.CompanionTheory.BZPhiPG.Stab.piPerm_false_val]; omega)
  · intro x
    have hxl := x.isLt
    have hcol : (Fin.last (i + (t + 1)) : Fin (i + (t + 1) + 1)) = ⟨(i + 1) + t, by omega⟩ :=
      Fin.ext (by rw [Fin.val_last, Fin.val_mk]; omega)
    rw [hcol]
    refine (GlobalTheory.CompanionTheory.BZPhiPG.Stab.castM_symm_entry hab r (i + x.val) ((i + 1) + t) (by omega) (by omega)
      (by omega) (by omega)).trans ?_
    exact GlobalTheory.CompanionTheory.BZPhiPG.Stab.entry_zero i t r d d' h hh e _ _
      (by rw [GlobalTheory.CompanionTheory.BZPhiPG.Stab.piPerm_true_val]; omega) (GlobalTheory.CompanionTheory.BZPhiPG.Cells.piPerm_last_val i t).le

end GlobalTheory.CompanionTheory.BZPhiPG.Stab

end
