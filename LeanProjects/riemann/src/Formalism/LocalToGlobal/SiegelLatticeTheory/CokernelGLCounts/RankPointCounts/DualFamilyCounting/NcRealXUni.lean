import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalJacobianOfDoubleCoset

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic

def sq2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem sq2_mul_sq2_eq_half : sq2 * sq2 = 1 / 2 := by
  unfold sq2
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

theorem star_sq2_eq_self : star sq2 = sq2 := by
  unfold sq2; rw [Complex.star_def, Complex.conj_ofReal]

def u1 (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val < r then sq2 else if r + k < i.val then -sq2 else 1

def u2 (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val < r then sq2 else if r + k < i.val then sq2 else 0

def Pu (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  (if j = i then u1 k r i else 0) + (if i = sig k r j then u2 k r i else 0)

theorem Pu_star (k r : ℕ) (i j : Fin (2 * r + k + 1)) : star (Pu k r i j) = Pu k r i j := by
  unfold Pu u1 u2
  split_ifs <;> simp [star_sq2_eq_self]

theorem PuJPu_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ((Pu k r)ᴴ * Formalism.REAL.Jm (epsK k r) * Pu k r) i j = Hpk k r i j := by
  have hJ : Formalism.REAL.Jm (epsK k r) = diagonal (dK k r) := rfl
  rw [hJ, mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, Pu_star]
  unfold Pu
  simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Hpk_eq]
  have hi := i.isLt
  have hs := sig_val k r i
  have h2 := sq2_mul_sq2_eq_half
  by_cases hji : j = i
  · subst hji
    simp only [Fin.ext_iff]
    simp only [u1, u2, dK, epsK, sgn, decide_eq_true_eq]
    split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
    all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
      linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
  · by_cases hjs : j = sig k r i
    · subst hjs
      simp only [sig_sig]
      have hji' : ¬ (sig k r i).val = i.val := fun h => hji (Fin.ext h)
      simp only [Fin.ext_iff]
      simp only [u1, u2, dK, epsK, sgn, decide_eq_true_eq]
      split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
      all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
        linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
    · have h1 : ¬ i = j := fun h => hji h.symm
      have h2' : ¬ i = sig k r j := fun h => hjs ((eq_sig_iff k r i j).1 h)
      have h3 : ¬ sig k r j = sig k r i := fun h => hji ((sig_inj k r j i).1 h)
      rw [if_neg h1, if_neg hjs, if_neg h2', if_neg h3, if_neg hjs]
      norm_num

theorem PuPu_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ((Pu k r)ᴴ * Pu k r) i j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j := by
  rw [mul_apply, one_apply]
  simp only [conjTranspose_apply, Pu_star]
  unfold Pu
  simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hi := i.isLt
  have hs := sig_val k r i
  have h2 := sq2_mul_sq2_eq_half
  by_cases hji : j = i
  · subst hji
    simp only [Fin.ext_iff]
    simp only [u1, u2]
    split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
    all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
      linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
  · by_cases hjs : j = sig k r i
    · subst hjs
      simp only [sig_sig]
      have hji' : ¬ (sig k r i).val = i.val := fun h => hji (Fin.ext h)
      simp only [Fin.ext_iff]
      simp only [u1, u2]
      split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
      all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
        linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
    · have h1 : ¬ i = j := fun h => hji h.symm
      have h2' : ¬ i = sig k r j := fun h => hjs ((eq_sig_iff k r i j).1 h)
      have h3 : ¬ sig k r j = sig k r i := fun h => hji ((sig_inj k r j i).1 h)
      simp [h1, hjs, h2', h3]

theorem PuJPu (k r : ℕ) : (Pu k r)ᴴ * Formalism.REAL.Jm (epsK k r) * Pu k r = Hpk k r := by
  ext i j; exact PuJPu_apply k r i j

theorem PuPu (k r : ℕ) : (Pu k r)ᴴ * Pu k r = 1 := by
  ext i j; exact PuPu_apply k r i j

theorem exists_unitary {r k : ℕ} (ε : Fin (2 * r + k + 1) → Bool)
    (hs : (Finset.univ.filter (fun i => ε i = false)).card = r + 1) :
    ∃ P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r ∧ Pᴴ * P = 1 := by
  obtain ⟨σ, hσ⟩ := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.PF.exists_perm ε hs
  refine ⟨Matrix.of fun i j => Pu k r (σ.symm i) j, ?_, ?_⟩
  · rw [← PuJPu k r]
    ext a b
    rw [mul_apply, mul_apply]
    simp only [Formalism.REAL.Jm, mul_diagonal, conjTranspose_apply, of_apply]
    refine (Fintype.sum_equiv σ _ _ (fun m => ?_)).symm
    simp only [Equiv.symm_apply_apply, hσ m]
  · rw [← PuPu k r]
    ext a b
    rw [mul_apply, mul_apply]
    simp only [conjTranspose_apply, of_apply]
    refine (Fintype.sum_equiv σ _ _ (fun m => ?_)).symm
    simp only [Equiv.symm_apply_apply]

end Formalism.L2.SG.Pf.NcReal.JX
