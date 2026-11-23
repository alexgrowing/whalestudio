import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.IotaProj

theorem blockIndex_succ_false (m j : ℕ) (a : Fin m) :
    eGP m (j + 1) ⟨false, a⟩ = (Fin.castSucc (eGP m j ⟨false, a⟩) : Fin (m + j + 1 + 1)) := by
  apply Fin.ext
  first
    | rfl
    | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]

theorem blockIndex_succ_true_castSucc (m j : ℕ) (b : Fin (j + 1)) :
    eGP m (j + 1) ⟨true, Fin.castSucc b⟩ = (Fin.castSucc (eGP m j ⟨true, b⟩) : Fin (m + j + 1 + 1)) := by
  apply Fin.ext
  first
    | rfl
    | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]
    | (simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]; omega)

theorem blockIndex_succ_true_last (m j : ℕ) :
    eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩ = (Fin.last (m + j + 1) : Fin (m + j + 1 + 1)) := by
  exact GlobalTheory.BZMir.Leib.blockIndex_true_last m (j + 1)

theorem glEmbMat_castSucc (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_castSucc (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (b : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc b) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_castSucc_last (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.last n) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_last (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) :
    glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem gpProj_iotaM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (y : MirabolicParabolic k m j) (hh : embedding₂ k (m + j) y ∈ MirabolicParabolic k m (j + 1)),
    gpProj k m (j + 1) ⟨_, hh⟩ = ((gpProj k m j y).1, embedding₂ k j (gpProj k m j y).2) := by
  intro k _ _ _ _ m j y hh
  refine Prod.ext ?_ ?_
  · refine Units.ext (Matrix.ext fun a b => ?_)
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m (j + 1))
      (GlobalTheory.BZMir.Leib.hgpIncl k m (j + 1) ⟨_, hh⟩) false a b).trans
      (Eq.trans ?_ (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
        (GlobalTheory.BZMir.Leib.hgpIncl k m j y) false a b).symm)
    rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_false m j a, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_false m j b]
    exact GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc k (m + j + 1)
      ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _
  · apply Subtype.ext
    refine Units.ext (Matrix.ext fun a b => ?_)
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m (j + 1))
      (GlobalTheory.BZMir.Leib.hgpIncl k m (j + 1) ⟨_, hh⟩) true a b).trans ?_
    have hR := fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j y) true a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_last]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_last k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)).trans
          (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_last k (j + 1)
            ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
              Matrix (Fin (j + 1)) (Fin (j + 1)) k)).symm
      | cast b =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_last, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_castSucc k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _).trans
          (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_castSucc k (j + 1)
            ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
              Matrix (Fin (j + 1)) (Fin (j + 1)) k) b).symm
    | cast a =>
      induction b using Fin.lastCases with
      | last =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_last, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc_last k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _).trans
          (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc_last k (j + 1)
            ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
              Matrix (Fin (j + 1)) (Fin (j + 1)) k) a).symm
      | cast b =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _).trans
          ((hR a b).symm.trans
            (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc k (j + 1)
              ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
                Matrix (Fin (j + 1)) (Fin (j + 1)) k) a b).symm)

end GlobalTheory.CompanionTheory.LeibPhi.IotaProj

end
