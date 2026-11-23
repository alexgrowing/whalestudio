import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb

theorem ePG_false_castSucc (i t : ℕ) (a : Fin (i + 1)) :
    ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ =
      (Fin.castSucc (eGP (i + 1) t ⟨false, a⟩) : Fin ((i + 1) + t + 1 + 1)) := by
  apply Fin.ext
  rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val]
  first
  | (simp [GlobalTheory.BZMir.Leib.ePG, finSumFinEquiv_symm_apply_castSucc]; done)
  | (have h1 : (finSumFinEquiv.symm (Fin.castSucc a) : Fin (i + 1) ⊕ Fin 1) = Sum.inl a :=
        finSumFinEquiv_symm_apply_castSucc a
     have h2 : GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ =
        finSumFinEquiv (Sum.map finSumFinEquiv (Equiv.refl (Fin 1))
          ((Equiv.sumAssoc (Fin (i + 1)) (Fin (t + 1)) (Fin 1)).symm
            (Sum.map (Equiv.refl (Fin (i + 1))) (Equiv.sumComm (Fin 1) (Fin (t + 1)))
              (Equiv.sumAssoc (Fin (i + 1)) (Fin 1) (Fin (t + 1))
                (Sum.inl (finSumFinEquiv.symm (Fin.castSucc a) : Fin (i + 1) ⊕ Fin 1)))))) := rfl
     rw [h2, h1]
     simp)

theorem ePG_true_eq (i t : ℕ) (b : Fin (t + 1)) :
    ePG (i + 1) (t + 1) ⟨true, b⟩ =
      (Fin.castSucc (eGP (i + 1) t ⟨true, b⟩) : Fin ((i + 1) + t + 1 + 1)) := by
  apply Fin.ext
  rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val]
  all_goals first | rfl | simp [GlobalTheory.BZMir.Leib.ePG]

section Ent

variable (k : Type) [Field k]

theorem glEmbMat_cc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
  first
  | (simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc]; done)
  | simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_lc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (b : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc b) = 0 := by
  first
  | (simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last, Fin.lastCases_castSucc]; done)
  | simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_cl (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.last n) = 0 := by
  first
  | (simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last, Fin.lastCases_castSucc]; done)
  | simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_ll (n : ℕ) (A : Matrix (Fin n) (Fin n) k) :
    glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
  first
  | (simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last]; done)
  | simp [GlobalTheory.BZMir.glEmbMat]

end Ent

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sEmb_mem_HPG (i t : ℕ) (h : MirabolicParabolic k (i + 1) t) :
    sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) ∈ HPG k (i + 1) (t + 1) := by
  have hh := (GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff k (i + 1) t
    (h : GlobalTheory.BZMir.Mir k ((i + 1) + t))).1 h.2
  have hentry : ∀ p q : Fin ((i + 1) + t + 1 + 1),
      (((GlobalTheory.CompanionTheory.BZPhiPG.sEmb k ((i + 1) + t) (h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) :
          GlobalTheory.BZMir.Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 1 + 1)) k) :
          Matrix (Fin ((i + 1) + t + 1 + 1)) (Fin ((i + 1) + t + 1 + 1)) k) p q =
        GlobalTheory.BZMir.glEmbMat k ((i + 1) + t + 1)
          (((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) :
            Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) p q := fun _ _ => rfl
  have hlast : GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1) ⟨false, Fin.last (i + 1)⟩ =
      Fin.last ((i + 1) + t + 1) := GlobalTheory.BZMir.Leib.ePG_false_last (i + 1) (t + 1)
  show ((GlobalTheory.CompanionTheory.BZPhiPG.sEmb k ((i + 1) + t) (h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) :
      GlobalTheory.BZMir.Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈
    GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1))
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro a b x y hba
  cases a <;> cases b
  all_goals first | exact absurd hba (by decide) | skip
  refine (hentry _ _).trans ?_
  obtain ⟨c, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last (y : Fin (i + 1 + 1))
  · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_true_eq,
      GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc,
      GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cc]
    exact hh x c
  · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_true_eq, hlast, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cl]

theorem sEmb_HGP_mem_HPG : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : MirabolicParabolic k (i + 1) t), ∃ η : HPG k (i + 1) (t + 1), (η : Mir k ((i + 1) + t + 1)) = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) ∧ pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1, (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)) := by
  intro k _ _ _ _ i t h
  let η : GlobalTheory.BZMir.Leib.HPG k (i + 1) (t + 1) :=
    ⟨GlobalTheory.CompanionTheory.BZPhiPG.sEmb k ((i + 1) + t) (h : GlobalTheory.BZMir.Mir k ((i + 1) + t)),
      GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.sEmb_mem_HPG k i t h⟩
  have hη : ∀ p q : Fin ((i + 1) + (t + 1) + 1),
      ((GlobalTheory.BZMir.Leib.hpgIncl k (i + 1) (t + 1) η : GL (Fin ((i + 1) + (t + 1) + 1)) k) :
          Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) p q =
        GlobalTheory.BZMir.glEmbMat k ((i + 1) + t + 1)
          (((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) :
            Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) p q := fun _ _ => rfl
  have hlast : GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1) ⟨false, Fin.last (i + 1)⟩ =
      Fin.last ((i + 1) + t + 1) := GlobalTheory.BZMir.Leib.ePG_false_last (i + 1) (t + 1)
  refine ⟨η, rfl, ?_⟩
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    apply Units.ext
    ext p q
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1))
      (GlobalTheory.BZMir.Leib.hpgIncl k (i + 1) (t + 1) η) false p q).trans ?_
    refine (hη _ _).trans ?_
    have hX : ∀ a b : Fin (i + 1),
        (((GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).1 : GL (Fin (i + 1)) k) :
            Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b =
          ((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)
            (GlobalTheory.BZMir.Leib.eGP (i + 1) t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.eGP (i + 1) t ⟨false, b⟩) :=
      fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP (i + 1) t)
        (GlobalTheory.BZMir.Leib.hgpIncl k (i + 1) t h) false a b
    have hL : ∀ a b : Fin (i + 1 + 1),
        (((GlobalTheory.BZMir.levi k (i + 1) (GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).1 :
            GlobalTheory.BZMir.Mir k (i + 1)) : GL (Fin (i + 1 + 1)) k) : Matrix (Fin (i + 1 + 1)) (Fin (i + 1 + 1)) k) a b =
          GlobalTheory.BZMir.glEmbMat k (i + 1)
            (((GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).1 : GL (Fin (i + 1)) k) :
              Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b := fun _ _ => rfl
    refine Eq.trans ?_ (hL _ _).symm
    obtain ⟨a, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last (p : Fin (i + 1 + 1)) <;>
    obtain ⟨b, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last (q : Fin (i + 1 + 1))
    · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc,
        GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc,
        GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cc, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cc]
      exact (hX a b).symm
    · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc, hlast,
        GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cl, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cl]
    · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc, hlast,
        GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_lc, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_lc]
    · rw [hlast, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_ll, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_ll]
  · apply Units.ext
    ext p q
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1))
      (GlobalTheory.BZMir.Leib.hpgIncl k (i + 1) (t + 1) η) true p q).trans ?_
    refine (hη _ _).trans ?_
    refine Eq.trans ?_ (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP (i + 1) t)
      (GlobalTheory.BZMir.Leib.hgpIncl k (i + 1) t h) true p q).symm
    rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_true_eq, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_true_eq,
      GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cc]
    rfl

end GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb

end
