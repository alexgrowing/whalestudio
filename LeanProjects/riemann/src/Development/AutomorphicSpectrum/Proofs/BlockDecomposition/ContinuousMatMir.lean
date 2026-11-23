import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZPhiPhi

variable (k : Type) [Field k]

def rowQ (n : ℕ) (g : Mir k (n + 1)) : Fin (n + 1) → k :=
  fun j => ((g : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k) (Fin.castSucc (Fin.last n)) (Fin.castSucc j)

def colQ (n : ℕ) (g : Mir k (n + 1)) : Fin (n + 1) → k :=
  fun i => ((g : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k) (Fin.castSucc i) (Fin.last (n + 1))

def unipM (n : ℕ) : Multiplicative (Fin (n + 1) → k) →* Mir k (n + 1) :=
  (unip k (n + 1)).codRestrict (Mir k (n + 1)) (fun v => MirU_le_Mir k (n + 1) ⟨v, rfl⟩)

theorem unipM_val (n : ℕ) (v : Multiplicative (Fin (n + 1) → k)) :
    ((unipM k n v : Mir k (n + 1)) : GL (Fin (n + 2)) k) = unip k (n + 1) v := rfl

theorem unipM_mem_MirUin (n : ℕ) (v : Multiplicative (Fin (n + 1) → k)) : unipM k n v ∈ MirUin k (n + 1) := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU]
  exact ⟨v, rfl⟩

end GlobalTheory.CompanionTheory.BZPhiPhi

namespace GlobalTheory.CompanionTheory.BZPhiPhi

variable (k : Type) [Field k]

theorem rowQ_one (n : ℕ) : rowQ k n 1 = Pi.single (Fin.last n) 1 := by
  funext j
  by_cases h : j = Fin.last n
  · subst h
    simp [GlobalTheory.CompanionTheory.BZPhiPhi.rowQ]
  · simp [GlobalTheory.CompanionTheory.BZPhiPhi.rowQ, Matrix.one_apply, Pi.single_apply, h, Ne.symm h]

end GlobalTheory.CompanionTheory.BZPhiPhi

namespace GlobalTheory.CompanionTheory.BZPhiPhi

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_matMir (n : ℕ) :
    Continuous fun g : Mir k (n + 1) => ((g : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_rowQ (n : ℕ) : Continuous (rowQ k n) :=
  continuous_pi fun j => (continuous_apply _).comp ((continuous_apply _).comp (continuous_matMir n))

theorem continuous_unipM (n : ℕ) :
    Continuous fun v : Fin (n + 1) → k => unipM k n (Multiplicative.ofAdd v) := by
  have hcol : Continuous fun v : Fin (n + 1) → k => GlobalTheory.BZMir.colMat k (n + 1) v := by
    refine continuous_matrix fun i j => ?_
    unfold GlobalTheory.BZMir.colMat
    by_cases hj : j = Fin.last (n + 1)
    · simp only [if_pos hj]
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · simp only [Fin.lastCases_castSucc]
        exact continuous_apply i
      · simp only [Fin.lastCases_last]
        exact continuous_const
    · simp only [if_neg hj]
      exact continuous_const
  have hval : Continuous fun v : Fin (n + 1) → k =>
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) k) + GlobalTheory.BZMir.colMat k (n + 1) v :=
    continuous_const.add hcol
  have hinv : Continuous fun v : Fin (n + 1) → k =>
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) k) - GlobalTheory.BZMir.colMat k (n + 1) v :=
    continuous_const.sub hcol
  have hGL : Continuous fun v : Fin (n + 1) → k =>
      GlobalTheory.BZMir.unip k (n + 1) (Multiplicative.ofAdd v) :=
    Units.continuous_iff.2 ⟨hval, hinv⟩
  exact hGL.subtype_mk _

end Top

end GlobalTheory.CompanionTheory.BZPhiPhi

end
