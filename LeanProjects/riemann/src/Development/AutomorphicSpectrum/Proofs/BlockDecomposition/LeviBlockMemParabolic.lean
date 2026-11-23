import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.QLevi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ePG_true_eq (i t : ℕ) (b : Fin t) :
    ePG i t ⟨true, b⟩ = Fin.castSucc (Fin.natAdd i b) := by
  apply Fin.ext
  simp [ePG]

theorem ePG_false_eq (i t : ℕ) (a : Fin i) :
    ePG i t ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd t a) := by
  apply Fin.ext
  simp [ePG, finSumFinEquiv_symm_apply_castSucc]

theorem two_true_eq (i t : ℕ) (b : Fin t) :
    two (stdSum (rfl : i + t = i + t)) ⟨true, b⟩ = Fin.natAdd i b := by
  apply Fin.ext
  simp

theorem two_false_eq (i t : ℕ) (a : Fin i) :
    two (stdSum (rfl : i + t = i + t)) ⟨false, a⟩ = Fin.castAdd t a := by
  apply Fin.ext
  simp

theorem levi_entry (n : ℕ) (g : GL (Fin n) k) (a b : Fin n) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.castSucc b) =
      (g : Matrix (Fin n) (Fin n) k) a b := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_entry_last_col (n : ℕ) (g : GL (Fin n) k) (a : Fin n) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.last n) = 0 := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_entry_last_row (n : ℕ) (g : GL (Fin n) k) (b : Fin n) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.castSucc b) = 0 := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_entry_last (n : ℕ) (g : GL (Fin n) k) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_mem_HPG (i t : ℕ) (q : Qp k i t) : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t := by
  show ((levi k (i + t) (q : GL (Fin (i + t)) k) : Mir k (i + t)) : GL (Fin (i + t + 1)) k) ∈ parab k (ePG i t)
  refine mem_parab_iff.2 ?_
  intro a c x y hac
  obtain ⟨rfl, rfl⟩ : a = true ∧ c = false := by
    revert hac; cases a <;> cases c <;> decide
  have hx : ePG i t ⟨true, x⟩ = Fin.castSucc (Fin.natAdd i (x : Fin t)) := ePG_true_eq i t x
  rw [hx]
  induction (y : Fin (i + 1)) using Fin.lastCases with
  | last =>
    rw [ePG_false_last]
    exact levi_entry_last_col _ _ _
  | cast y =>
    rw [ePG_false_eq, levi_entry]
    have := mem_parab_iff.1 q.2 true false (x : Fin t) (y : Fin i) (by decide)
    rwa [two_true_eq, two_false_eq] at this

theorem pgProj_levi (i t : ℕ) (q : Qp k i t) (h : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t) :
    pgProj k i t ⟨_, h⟩ = (levi k i (qBlocks k i t q).1, (qBlocks k i t q).2) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Units.ext
    ext a b
    show (leviProj k (ePG i t) (hpgIncl k i t ⟨_, h⟩) false : GL (Fin (i + 1)) k).val a b =
      ((levi k i (qBlocks k i t q).1 : GL (Fin (i + 1)) k) : Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b
    rw [leviProj_apply]
    show ((levi k (i + t) (q : GL (Fin (i + t)) k) : GL (Fin (i + t + 1)) k) : Matrix _ _ k)
      (ePG i t ⟨false, a⟩) (ePG i t ⟨false, b⟩) = _
    induction a using Fin.lastCases with
    | last =>
      rw [ePG_false_last]
      induction b using Fin.lastCases with
      | last => rw [ePG_false_last, levi_entry_last, levi_entry_last]
      | cast b => rw [ePG_false_eq, levi_entry_last_row, levi_entry_last_row]
    | cast a =>
      rw [ePG_false_eq]
      induction b using Fin.lastCases with
      | last => rw [ePG_false_last, levi_entry_last_col, levi_entry_last_col]
      | cast b =>
        rw [ePG_false_eq, levi_entry, levi_entry]
        show _ = (leviProj k (two (stdSum (rfl : i + t = i + t))) q false : GL (Fin i) k).val a b
        rw [leviProj_apply, two_false_eq, two_false_eq]
  · apply Units.ext
    ext a b
    show (leviProj k (ePG i t) (hpgIncl k i t ⟨_, h⟩) true : GL (Fin t) k).val a b =
      (leviProj k (two (stdSum (rfl : i + t = i + t))) q true : GL (Fin t) k).val a b
    rw [leviProj_apply, leviProj_apply]
    show ((levi k (i + t) (q : GL (Fin (i + t)) k) : GL (Fin (i + t + 1)) k) : Matrix _ _ k)
      (ePG i t ⟨true, a⟩) (ePG i t ⟨true, b⟩) = _
    rw [ePG_true_eq, ePG_true_eq, levi_entry, two_true_eq, two_true_eq]

end GlobalTheory.CompanionTheory.BZPsiPG.QLevi

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem levi_Qp_mem_pgProj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) (q : Qp k i t) :
    ∃ h : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t,
      pgProj k i t ⟨_, h⟩ = (levi k i (qBlocks k i t q).1, (qBlocks k i t q).2) :=
  ⟨QLevi.levi_mem_HPG i t q, QLevi.pgProj_levi i t q _⟩

end GlobalTheory.CompanionTheory.BZPsiPG

end
