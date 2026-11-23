import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjShiftedEmbedding
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.EtaConj

open GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem castM_val {a b : ℕ} (e : a = b) (m : Mir k a) (x y : Fin (b + 1)) :
    ((castM k e m : Mir k b) : GL (Fin (b + 1)) k).val x y =
      (m : GL (Fin (a + 1)) k).val (Fin.cast (by omega) x) (Fin.cast (by omega) y) := by
  subst e
  rfl

theorem piPerm_cast (i t : ℕ) (s : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    piPerm i t (Fin.cast (by omega) (ePG i (t + 1) s)) = eGP (i + 1) t s := by
  show eGP (i + 1) t ((ePG i (t + 1)).symm (Fin.cast (by omega) (Fin.cast (by omega) (ePG i (t + 1) s)))) = _
  simp

theorem conj_entry (i t : ℕ) (r : GL (Fin ((i + 1) + t + 1)) k) (x y : Fin ((i + 1) + t + 1)) :
    (wGL k i t * r * (wGL k i t)⁻¹).val (piPerm i t x) (piPerm i t y) = r.val x y := by
  show (Equiv.Perm.permMatrix k (piPerm i t)⁻¹ * r.val * Equiv.Perm.permMatrix k (piPerm i t)) _ _ = _
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]

theorem conj_block (i t : ℕ) (h : Mir k (i + (t + 1))) (s s' : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    (wGL k i t * ((castM k (by omega) h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹).val
        (eGP (i + 1) t s) (eGP (i + 1) t s') =
      (h : GL (Fin (i + (t + 1) + 1)) k).val (ePG i (t + 1) s) (ePG i (t + 1) s') := by
  rw [← piPerm_cast, ← piPerm_cast, conj_entry, castM_val]
  rfl

theorem eta_val (i t : ℕ) (m : Mir k ((i + 1) + t)) (x y : Fin ((i + 1) + t + 1 + 1)) :
    ((wEl k i t * sEmb k ((i + 1) + t) m * (wEl k i t)⁻¹ : Mir k ((i + 1) + t + 1)) :
        GL (Fin ((i + 1) + t + 1 + 1)) k).val x y =
      glEmbMat k ((i + 1) + t + 1) (wGL k i t * (m : GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹).val x y := by
  have e : wEl k i t * sEmb k ((i + 1) + t) m * (wEl k i t)⁻¹ =
      levi k _ (wGL k i t * (m : GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹) := by
    simp only [map_mul, map_inv]
    rfl
  rw [e]
  rfl

theorem eta_mem (i t : ℕ) (h : HPG k i (t + 1)) :
    wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ ∈
      HPG k (i + 1) (t + 1) := by
  have hh := mem_parab_iff.1 (show ((h : Mir k (i + (t + 1))) : GL (Fin (i + (t + 1) + 1)) k) ∈ parab k (ePG i (t + 1)) from h.2)
  show ((wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ :
    Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ parab k (ePG (i + 1) (t + 1))
  rw [mem_parab_iff]
  intro x y b a hxy
  cases x <;> cases y <;> first | exact absurd hxy (by decide) | skip
  refine (eta_val i t _ _ _).trans ?_
  rw [ePG_true_eq]
  induction a using Fin.lastCases with
  | last =>
    rw [ePG_false_last]
    exact glEmbMat_cl k _ _ _
  | cast a =>
    rw [ePG_false_castSucc, glEmbMat_cc, conj_block]
    exact hh true false b a hxy

theorem eta_mem_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : HPG k i (t + 1)),
  ∃ hη : wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ ∈ HPG k (i + 1) (t + 1),
    pgProj k (i + 1) (t + 1) ⟨_, hη⟩ = (sEmb k i (pgProj k i (t + 1) h).1, (pgProj k i (t + 1) h).2) := by
  intro k _ _ _ _ i t h
  refine ⟨eta_mem i t h, ?_⟩
  have hent : ∀ x z : Fin ((i + 1) + t + 1 + 1),
      ((hpgIncl k (i + 1) (t + 1) ⟨_, eta_mem i t h⟩ : parab k (ePG (i + 1) (t + 1))) :
        GL (Fin ((i + 1) + (t + 1) + 1)) k).val x z =
        glEmbMat k ((i + 1) + t + 1) (wGL k i t * ((castM k (by omega) (h : Mir k (i + (t + 1))) : Mir k ((i + 1) + t)) :
          GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹).val x z :=
    fun x z => eta_val i t _ x z
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    apply Units.ext
    ext a b
    show (leviProj k (ePG (i + 1) (t + 1)) (hpgIncl k (i + 1) (t + 1) ⟨_, eta_mem i t h⟩) false).val a b =
      glEmbMat k (i + 1) (leviProj k (ePG i (t + 1)) (hpgIncl k i (t + 1) h) false).val a b
    rw [leviProj_apply, hent]
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last =>
        rw [ePG_false_last]
        exact (glEmbMat_ll k _ _).trans (glEmbMat_ll k _ _).symm
      | cast b =>
        rw [ePG_false_last, ePG_false_castSucc]
        exact (glEmbMat_lc k _ _ _).trans (glEmbMat_lc k _ _ _).symm
    | cast a =>
      induction b using Fin.lastCases with
      | last =>
        rw [ePG_false_last, ePG_false_castSucc]
        exact (glEmbMat_cl k _ _ _).trans (glEmbMat_cl k _ _ _).symm
      | cast b =>
        rw [ePG_false_castSucc, ePG_false_castSucc, glEmbMat_cc, glEmbMat_cc, leviProj_apply, conj_block]
        rfl
  · apply Units.ext
    ext a b
    show (leviProj k (ePG (i + 1) (t + 1)) (hpgIncl k (i + 1) (t + 1) ⟨_, eta_mem i t h⟩) true).val a b =
      (leviProj k (ePG i (t + 1)) (hpgIncl k i (t + 1) h) true).val a b
    rw [leviProj_apply, hent, ePG_true_eq, ePG_true_eq, glEmbMat_cc, leviProj_apply, conj_block]
    rfl

end GlobalTheory.CompanionTheory.BZPhiPG.EtaConj

end
