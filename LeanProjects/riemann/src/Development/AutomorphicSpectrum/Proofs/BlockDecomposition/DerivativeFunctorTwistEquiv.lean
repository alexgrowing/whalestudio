import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhiTw

variable {k : Type} [Field k]

theorem twKer_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (χ : G →* ℂˣ)
    (h : ∀ n : N, χ (n : G) = 1) : twKer (twist ρ χ) N θ = twKer ρ N θ := by
  unfold twKer
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, twist_apply, h, Units.val_one, one_smul]

theorem det_glEmbMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : (glEmbMat k n A).det = A.det := by
  rw [Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
  have h0 : ∀ i : Fin n, glEmbMat k n A (Fin.last n) (Fin.castSucc i) = 0 := fun i => by
    simp [glEmbMat]
  have h1 : glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by simp [glEmbMat]
  have h2 : (glEmbMat k n A).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = A := by
    ext i j
    simp [glEmbMat]
  simp only [h0, h1, h2]
  simp [← two_mul, pow_mul]

theorem det_unip (n : ℕ) (v : Multiplicative (Fin n → k)) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1 := by
  have e : ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + colMat k n v.toAdd := rfl
  rw [e, Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    induction i using Fin.lastCases with
    | last => simp [colMat]
    | cast i => simp [colMat, Fin.castSucc_ne_last]
  · intro i j hij
    have hij' : j < i := hij
    have hne : i ≠ j := (ne_of_lt hij').symm
    have hj : j ≠ Fin.last n := (lt_of_lt_of_le hij' (Fin.le_last i)).ne
    simp [colMat, hj, hne]

section Local

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dpowM_unip (n : ℕ) (t : ℝ) (u : MirUin k n) : dpowM n t (u : Mir k n) = 1 := by
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hd : Matrix.GeneralLinearGroup.det ((u : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
    have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
    ext1
    rw [hv']
    exact det_unip n v
  show dpow (n + 1) t ((u : Mir k n) : GL (Fin (n + 1)) k) = 1
  rw [dpow, detChar_apply, hd, map_one]

theorem dpowM_levi (n : ℕ) (t : ℝ) (p : Mir k n) :
    dpowM (n + 1) t ((levi k (n + 1)).comp (Mir k n).subtype p) = dpowM n t p := by
  have hd : Matrix.GeneralLinearGroup.det (glEmb k (n + 1) (p : GL (Fin (n + 1)) k)) =
      Matrix.GeneralLinearGroup.det (p : GL (Fin (n + 1)) k) := by
    ext1
    exact det_glEmbMat (n + 1) _
  show dpow (n + 2) t (glEmb k (n + 1) (p : GL (Fin (n + 1)) k)) = dpow (n + 1) t (p : GL (Fin (n + 1)) k)
  rw [dpow, dpow, detChar_apply, detChar_apply, hd]

theorem phiMinus_twist_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (j : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k (j + 1)) W) (t : ℝ),
    Nonempty ((phiMinus k ψ (twist τ (dpowM (j + 1) t))).Equiv (twist (phiMinus k ψ τ) (dpowM j t))) := by
  intro k _ _ _ _ ψ j W _ _ τ t
  have hK := twKer_twist τ (MirUin k (j + 1)) (mirChar k ψ j) (dpowM (j + 1) t) (dpowM_unip (j + 1) t)
  refine ⟨Representation.Equiv.mk (Submodule.quotEquivOfEq _ _ hK) fun p => ?_⟩
  apply Submodule.linearMap_qext
  ext v
  show Submodule.Quotient.mk ((twist τ (dpowM (j + 1) t)) ((levi k (j + 1)).comp (Mir k j).subtype p) v) =
    twist (phiMinus k ψ τ) (dpowM j t) p (Submodule.Quotient.mk v)
  rw [twist_apply, twist_apply, dpowM_levi]
  rfl

end Local

end GlobalTheory.CompanionTheory.LeibPhiTw

end
