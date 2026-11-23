import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

variable {k : Type} [Field k]

theorem sEmb_mul_row (n : ℕ) (m : Mir k n) (q : Mir k (n + 1)) (j : Fin (n + 1 + 1)) :
    (((sEmb k n m * q : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k)
        (Fin.castSucc (Fin.last n)) j =
      ((q : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) (Fin.castSucc (Fin.last n)) j := by
  have hm : ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) =
      GlobalTheory.BZMir.eLast k n :=
    (GlobalTheory.BZMir.mem_Mir_iff k (m : GL (Fin (n + 1)) k)).1 m.2
  have hm' : ∀ x, ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) x =
      GlobalTheory.BZMir.eLast k n x := fun x => congrFun hm x
  have he : (((GlobalTheory.CompanionTheory.BZPhiPG.sEmb k n m : GlobalTheory.BZMir.Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) :
      Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) =
      GlobalTheory.BZMir.glEmbMat k (n + 1) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    rfl
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [he, Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc, Fin.lastCases_last, hm', zero_mul,
    add_zero, GlobalTheory.BZMir.eLast]
  simp [Pi.single_apply]

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

theorem GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) :
    ∀ p ∈ Cl k i t, ∀ m, p * sO k i t m ∈ Cl k i t := by
  intro p hp m
  have key : ∀ j, (((GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sO k i t m⁻¹ * p⁻¹ : GlobalTheory.BZMir.Mir k (i + 1 + t + 1)) :
      GL (Fin (i + 1 + t + 1 + 1)) k) : Matrix (Fin (i + 1 + t + 1 + 1)) (Fin (i + 1 + t + 1 + 1)) k)
        (Fin.castSucc (Fin.last (i + 1 + t))) j =
      (((p⁻¹ : GlobalTheory.BZMir.Mir k (i + 1 + t + 1)) : GL (Fin (i + 1 + t + 1 + 1)) k) :
        Matrix (Fin (i + 1 + t + 1 + 1)) (Fin (i + 1 + t + 1 + 1)) k) (Fin.castSucc (Fin.last (i + 1 + t))) j :=
    fun j => GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sEmb_mul_row (i + 1 + t)
      (GlobalTheory.CompanionTheory.BZPhiPG.castM k (by omega) m⁻¹) p⁻¹ j
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.Cl, Set.mem_setOf_eq] at hp ⊢
  intro c
  rw [_root_.mul_inv_rev, ← map_inv (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sO k i t) m]
  exact (key _).trans (hp c)
