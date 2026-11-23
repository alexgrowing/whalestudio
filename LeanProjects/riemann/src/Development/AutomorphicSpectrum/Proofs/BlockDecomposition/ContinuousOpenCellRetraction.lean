import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirProj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Proj

section Alg

variable (k : Type) [Field k]

def rGL {a b : ℕ} (h : a = b) : GL (Fin a) k ≃* GL (Fin b) k := h ▸ MulEquiv.refl _

theorem rGL_apply {a b : ℕ} (h : a = b) (g : GL (Fin a) k) (r c : Fin b) :
    ((rGL k h g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k) r c =
      (g : Matrix (Fin a) (Fin a) k) (Fin.cast h.symm r) (Fin.cast h.symm c) := by
  subst h
  rfl

theorem rGL_rGL {a b : ℕ} (h : a = b) (h' : b = a) (g : GL (Fin a) k) : rGL k h' (rGL k h g) = g := by
  subst h
  rfl

theorem continuous_rGL [TopologicalSpace k] {a b : ℕ} (h : a = b) : Continuous (rGL k h) := by
  subst h
  exact continuous_id

theorem castM_val {a b : ℕ} (h : a = b) (h' : a + 1 = b + 1) (M : Mir k a) :
    ((castM k h M : Mir k b) : GL (Fin (b + 1)) k) = rGL k h' (M : GL (Fin (a + 1)) k) := by
  subst h
  rfl

theorem mirProj_eq_one_of_unip (n : ℕ) (u : Mir k n) (v : Multiplicative (Fin n → k))
    (hu : (u : GL (Fin (n + 1)) k) = unip k n v) : mirabolicProjection k n u = 1 := by
  ext i j
  show blockMat k n ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j = _
  rw [hu]
  simp [blockMat, unip, colMat, Fin.castSucc_ne_last, one_apply]

theorem ePG_true_val (i t : ℕ) (b : Fin t) : ((ePG i t ⟨true, b⟩ : Fin (i + t + 1)) : ℕ) = i + b := by
  simp [ePG]

theorem ePG_false_castSucc_val (i t : ℕ) (a : Fin i) :
    ((ePG i t ⟨false, Fin.castSucc a⟩ : Fin (i + t + 1)) : ℕ) = a := by
  simp [ePG, finSumFinEquiv_symm_apply_castSucc]

theorem wGL_conj_apply (i t : ℕ) (A : GL (Fin ((i + 1) + t + 1)) k) (r c : Fin ((i + 1) + t + 1)) :
    (((wGL k i t)⁻¹ * A * wGL k i t : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) r c =
      (A : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) (piPerm i t r) (piPerm i t c) := by
  have e1 : (((wGL k i t)⁻¹ : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) = Equiv.Perm.permMatrix k (piPerm i t) := rfl
  have e2 : ((wGL k i t : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) = Equiv.Perm.permMatrix k (piPerm i t)⁻¹ := rfl
  rw [Units.val_mul, Units.val_mul, e1, e2, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp [Matrix.submatrix_apply, Equiv.Perm.inv_def]

theorem piPerm_cast (i t : ℕ) (s : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) (h : i + (t + 1) + 1 = (i + 1) + t + 1) :
    piPerm i t (Fin.cast h (ePG i (t + 1) s)) = eGP (i + 1) t s := by
  simp [piPerm]

theorem proj_eq (i t : ℕ) (h : Mir k ((i + 1) + t + 1)) (d : Fin (t + 1) → k) (M : Mir k ((i + 1) + t))
    (x : Mir k ((i + 1) + t + 1))
    (e : dEmb k i t d * wEl k i t * sEmb k _ M = h * wEl k i t * x) :
    (M : GL (Fin ((i + 1) + t + 1)) k) =
      ((wGL k i t)⁻¹ * mirabolicProjection k _ h * wGL k i t) * mirabolicProjection k _ x := by
  have e1 := congrArg (mirabolicProjection k ((i + 1) + t + 1)) e
  rw [map_mul, map_mul, map_mul, map_mul] at e1
  have h1 : mirabolicProjection k ((i + 1) + t + 1) (dEmb k i t d) = 1 := mirProj_eq_one_of_unip k _ _ _ rfl
  have h2 : mirabolicProjection k ((i + 1) + t + 1) (wEl k i t) = wGL k i t := GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi k _ _
  have h3 : mirabolicProjection k ((i + 1) + t + 1) (sEmb k _ M) = (M : GL (Fin ((i + 1) + t + 1)) k) :=
    GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi k _ _
  rw [h1, h2, h3, one_mul] at e1
  rw [mul_assoc, mul_assoc, eq_inv_mul_iff_mul_eq, e1, mul_assoc]

end Alg

theorem exists_parab_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), ∃ Θ : Mir k ((i + 1) + t + 1) → GL (Fin (i + (t + 1) + 1)) k, Continuous Θ ∧ Θ 1 = 1 ∧
    ∀ (h : Mir k ((i + 1) + (t + 1))), h ∈ HPG k (i + 1) (t + 1) → ∀ (d : Fin (t + 1) → k) (m : Mir k (i + (t + 1)))
      (x : Mir k ((i + 1) + t + 1)), dEmb k i t d * wEl k i t * sO k i t m = h * wEl k i t * x →
      ∃ p ∈ parab k (ePG i (t + 1)), (m : GL (Fin (i + (t + 1) + 1)) k) = p * Θ x := by
  intro k _ _ _ _ i t
  have hn : (i + 1) + t + 1 = i + (t + 1) + 1 := by omega
  refine ⟨fun x => rGL k hn (mirabolicProjection k _ x),
    (continuous_rGL k hn).comp (GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k _), by simp, ?_⟩
  intro h hh d m x e
  have e2 := proj_eq k i t h d (castM k (by omega) m) x e
  rw [castM_val k _ hn.symm] at e2
  refine ⟨rGL k hn ((wGL k i t)⁻¹ * mirabolicProjection k _ h * wGL k i t), ?_, ?_⟩
  · rw [mem_parab_iff]
    intro a b u v hab
    cases a <;> cases b <;> first | exact absurd hab (by decide) | skip
    rw [rGL_apply, wGL_conj_apply, piPerm_cast, piPerm_cast]
    have hh' : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ parab k (ePG (i + 1) (t + 1)) := hh
    have h0 := mem_parab_iff.1 hh' true false u (Fin.castSucc v) (by decide)
    have e3 : Fin.castSucc (eGP (i + 1) t ⟨true, u⟩) = ePG (i + 1) (t + 1) ⟨true, u⟩ :=
      Fin.ext (by rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val, ePG_true_val])
    have e4 : Fin.castSucc (eGP (i + 1) t ⟨false, v⟩) = ePG (i + 1) (t + 1) ⟨false, Fin.castSucc v⟩ :=
      Fin.ext (by rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val, ePG_false_castSucc_val])
    show ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val
      (Fin.castSucc (eGP (i + 1) t ⟨true, u⟩)) (Fin.castSucc (eGP (i + 1) t ⟨false, v⟩)) = 0
    rw [e3, e4]
    exact h0
  · have e5 := congrArg (rGL k hn) e2
    rw [rGL_rGL, map_mul] at e5
    exact e5

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Proj
