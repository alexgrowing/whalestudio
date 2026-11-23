import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem piPerm_last_val (i t : ℕ) : ((piPerm i t (Fin.last ((i + 1) + t)) : Fin ((i + 1) + t + 1)) : ℕ) = i := by
  have key : ∀ x : Fin (i + (t + 1) + 1), (x : ℕ) = i + 1 + t →
      ((GlobalTheory.BZMir.Leib.eGP (i + 1) t ((GlobalTheory.BZMir.Leib.ePG i (t + 1)).symm x) :
        Fin ((i + 1) + t + 1)) : ℕ) = i := by
    intro x hx
    have hxl : x = Fin.last (i + (t + 1)) := Fin.ext (by rw [Fin.val_last]; omega)
    subst hxl
    have h2 : (GlobalTheory.BZMir.Leib.ePG i (t + 1)).symm (Fin.last (i + (t + 1))) =
        ⟨false, Fin.last i⟩ := by
      rw [Equiv.symm_apply_eq, GlobalTheory.BZMir.Leib.ePG_false_last]
    rw [h2]
    exact GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val (i + 1) t (Fin.last i)
  first
    | (simp only [GlobalTheory.CompanionTheory.BZPhiPG.piPerm, Equiv.trans_apply]; exact key _ rfl)
    | exact key _ rfl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem wEl_inv_entry (i t : ℕ) (c : Fin ((i + 1) + t + 1)) (hc : (c : ℕ) = i) :
    ((((wEl k i t)⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castSucc c) = 1 := by
  have hσ : GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t (Fin.last ((i + 1) + t)) = c :=
    Fin.ext ((GlobalTheory.CompanionTheory.BZPhiPG.OntoO.piPerm_last_val i t).trans hc.symm)
  rw [GlobalTheory.CompanionTheory.BZPhiPG.wEl, ← map_inv]
  change GlobalTheory.BZMir.glEmbMat k ((i + 1) + t + 1)
      (((GlobalTheory.CompanionTheory.BZPhiPG.wGL k i t)⁻¹ : GL (Fin ((i + 1) + t + 1)) k) :
        Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k)
      (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castSucc c) = 1
  simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc]
  change Equiv.Perm.permMatrix k (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t) (Fin.last ((i + 1) + t)) c = 1
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hσ]

theorem dEmb_zero (i t : ℕ) : dEmb k i t 0 = 1 := by
  have h : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
    funext j
    refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · rw [Fin.append_left]; rfl
    · rw [Fin.append_right]; rfl
  apply Subtype.ext
  change GlobalTheory.BZMir.unip k ((i + 1) + (t + 1))
      (Multiplicative.ofAdd (Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k))) = 1
  rw [h, ofAdd_zero, map_one]

theorem wEl_notMem_Cl (i t : ℕ) : wEl k i t ∉ Cl k i t := by
  intro hmem
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.Cl, Set.mem_setOf_eq] at hmem
  have h := hmem (Fin.last i)
  have hc : (Fin.castLE (by omega) (Fin.last i) : Fin ((i + 1) + t + 1 + 1)) =
      Fin.castSucc (⟨i, by omega⟩ : Fin ((i + 1) + t + 1)) := Fin.ext rfl
  rw [hc, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.wEl_inv_entry k i t ⟨i, by omega⟩ rfl] at h
  exact one_ne_zero h

theorem wEl_notMem_Cl_and_dEmb_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ), wEl k i t ∉ Cl k i t ∧ dEmb k i t 0 = 1 := by
  intro k _ _ _ _ i t
  exact ⟨GlobalTheory.CompanionTheory.BZPhiPG.OntoO.wEl_notMem_Cl k i t, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.dEmb_zero k i t⟩

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end
