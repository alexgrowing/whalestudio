import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SecWFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.S.Pv.SecW

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

variable {n r k : ℕ}

def sfv (sc : ℝ) (b : Fin r) : ℂ := ((sc : ℂ) ^ (r - b.1))⁻¹

def lamv (sc : ℝ) (c : Fin (r + 1) → ℂ) (b : Fin r) : ℂ := c (Fin.castSucc b) / (sfv sc b * sfv sc b)

def alv (T : ℝ) (c : Fin (r + 1) → ℂ) : ℂ := -c (Fin.last r) / (T : ℂ)

def bev (T T' : ℝ) (c : Fin (r + 1) → ℂ) : ℂ := ((Real.sqrt (‖c (Fin.last r)‖ ^ 2 / T - T') : ℝ) : ℂ)

def svv (T T' : ℝ) : ℂ := (((Real.sqrt (T * T'))⁻¹ : ℝ) : ℂ)

def e2 (sc : ℝ) (c : Fin (r + 1) → ℂ) (f : Fin r → Fin n → ℂ) : Fin r → Fin n → ℂ :=
  fun b => lamv sc c b • f b

def p2 (sc : ℝ) (c : Fin (r + 1) → ℂ) (e : Fin r → Fin n → ℂ) : Fin r → Fin n → ℂ :=
  fun b => (conj (lamv sc c b))⁻¹ • e b

def z2 (T T' : ℝ) (c : Fin (r + 1) → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) (i0 : Fin k) : Fin n → ℂ :=
  alv T c • z + bev T T' c • w i0

def w2 (T T' : ℝ) (c : Fin (r + 1) → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) (i0 : Fin k) :
    Fin k → Fin n → ℂ :=
  fun j => if j = i0 then svv T T' • (bev T T' c • z + (conj (alv T c) * (T : ℂ)) • w i0) else w j

section Facts

variable {sc T T' : ℝ} {c : Fin (r + 1) → ℂ}

theorem conj_sfv (sc : ℝ) (b : Fin r) : conj (sfv sc b) = sfv sc b := by
  simp only [sfv, map_inv₀, map_pow, Complex.conj_ofReal]

theorem sfv_ne (hsc : 0 < sc) (b : Fin r) : sfv sc b ≠ 0 :=
  inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hsc.ne'))

theorem lamv_ne (hsc : 0 < sc) (hc : ∀ l, c l ≠ 0) (b : Fin r) : lamv sc c b ≠ 0 :=
  div_ne_zero (hc _) (mul_ne_zero (sfv_ne hsc b) (sfv_ne hsc b))

theorem conj_bev (T T' : ℝ) (c : Fin (r + 1) → ℂ) : conj (bev T T' c) = bev T T' c := Complex.conj_ofReal _

theorem bev_sq (hT : 0 < T) (hg : 0 < ‖c (Fin.last r)‖ ^ 2 - T * T') :
    conj (bev T T' c) * bev T T' c = ((‖c (Fin.last r)‖ ^ 2 / T - T' : ℝ) : ℂ) := by
  have hq0 : 0 ≤ ‖c (Fin.last r)‖ ^ 2 / T - T' := by
    rw [div_sub' hT.ne']
    exact div_nonneg (by nlinarith) hT.le
  rw [conj_bev, bev, ← Complex.ofReal_mul, Real.mul_self_sqrt hq0]

theorem alv_sq (T : ℝ) (c : Fin (r + 1) → ℂ) :
    conj (alv T c) * alv T c = ((‖c (Fin.last r)‖ ^ 2 / T ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, alv, map_div₀, map_neg, Complex.conj_ofReal, neg_div, neg_div, neg_mul_neg, div_mul_div_comm,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem svv_sq (hT : 0 < T) (hT' : 0 < T') : conj (svv T T') * svv T T' = ((1 / (T * T') : ℝ) : ℂ) := by
  rw [svv, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by positivity), one_div]

end Facts

section Frame

variable {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {w : Fin k → Fin n → ℂ}
  {sc T T' : ℝ} {c : Fin (r + 1) → ℂ}

theorem frm2 (F0 : Frm ε e f z w T) (hT : 0 < T) (hT' : 0 < T') (hsc : 0 < sc) (hc : ∀ l, c l ≠ 0)
    (hg : 0 < ‖c (Fin.last r)‖ ^ 2 - T * T') (i0 : Fin k) :
    Frm ε (e2 sc c f) (p2 sc c e) (z2 T T' c z w i0) (w2 T T' c z w i0) T' := by
  have hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [hJ_swapδ F0.ep b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have hwz : ∀ j, hJ ε (w j) z = 0 := fun j => hJ_swap0 (F0.zw j)
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hT'c : (T' : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
  have hlam := lamv_ne hsc hc
  have hcb := conj_bev T T' c
  have hβ := bev_sq (T' := T') hT hg
  rw [hcb] at hβ
  have hα := alv_sq T c
  have hs := svv_sq hT hT'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hT'.ne'⟩
  · intro a b
    simp only [e2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, F0.pp, mul_zero]
  · intro a b
    simp only [e2, p2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, hfe]
    split_ifs with h
    · subst h
      rw [mul_one, inv_mul_cancel₀ ((map_ne_zero _).2 (hlam a))]
    · simp
  · intro a b
    simp only [p2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, F0.ee, mul_zero]
  · intro a
    simp only [e2, z2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, F0.pz, F0.pw, mul_zero,
      add_zero]
  · intro a
    simp only [p2, z2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, F0.ez, F0.ew, mul_zero,
      add_zero]
  · simp only [z2, UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, F0.zz,
      F0.zw, hwz, F0.ww, if_true, mul_zero, add_zero, zero_add, mul_one, hcb]
    linear_combination (norm := skip) (-(T : ℂ)) * hα + hβ
    push_cast
    field_simp
    ring
  · intro a j
    by_cases hj : j = i0
    · simp only [e2, w2, if_pos hj, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_add_right, F0.pz, F0.pw,
        mul_zero, add_zero]
    · simp only [e2, w2, if_neg hj, UnitaryIsometries.hJ_smul_left, F0.pw, mul_zero]
  · intro a j
    by_cases hj : j = i0
    · simp only [p2, w2, if_pos hj, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_add_right, F0.ez, F0.ew,
        mul_zero, add_zero]
    · simp only [p2, w2, if_neg hj, UnitaryIsometries.hJ_smul_left, F0.ew, mul_zero]
  · intro j
    by_cases hj : j = i0
    · simp only [z2, w2, if_pos hj, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_add_right,
        UnitaryIsometries.hJ_smul_left, F0.zz, F0.zw, hwz, F0.ww, if_true, mul_zero, add_zero, zero_add, mul_one, hcb]
      ring
    · have hne : i0 ≠ j := fun h => hj h.symm
      simp only [z2, w2, if_neg hj, UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_smul_left, F0.zw, F0.ww, if_neg hne, mul_zero,
        add_zero]
  · intro i j
    by_cases hi : i = i0 <;> by_cases hj : j = i0
    · subst hi; subst hj
      simp only [w2, if_true, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_left,
        F0.zz, F0.zw, hwz, F0.ww, mul_zero, add_zero, zero_add, mul_one, hcb, map_mul, Complex.conj_conj,
        Complex.conj_ofReal]
      linear_combination (norm := skip) ((T : ℂ) ^ 2 * (conj (alv T c) * alv T c) - (T : ℂ) * (bev T T' c * bev T T' c)) * hs +
        (((1 / (T * T') : ℝ) : ℂ) * (T : ℂ) ^ 2) * hα - (((1 / (T * T') : ℝ) : ℂ) * (T : ℂ)) * hβ
      push_cast
      field_simp
      ring
    · subst hi
      have hne : i ≠ j := fun h => hj h.symm
      simp only [w2, if_true, if_neg hj, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_add_left, F0.zw, F0.ww, if_neg hne,
        mul_zero, add_zero]
    · subst hj
      have hne : i ≠ j := hi
      simp only [w2, if_true, if_neg hi, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_add_right, hwz, F0.ww, if_neg hne,
        mul_zero, add_zero]
    · simp only [w2, if_neg hi, if_neg hj]
      exact F0.ww i j

end Frame

end Formalism.L2.S.Pv.SecW
