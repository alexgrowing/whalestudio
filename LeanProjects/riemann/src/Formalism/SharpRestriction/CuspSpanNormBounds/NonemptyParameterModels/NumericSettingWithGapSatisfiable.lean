import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature

noncomputable section

namespace Formalism.MainNotions.S.Inh

section obj

open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

def invSqrtTwoComplex : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

lemma obj_s_sq : invSqrtTwoComplex * invSqrtTwoComplex = 1 / 2 := by
  unfold invSqrtTwoComplex
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma obj_s_star : star invSqrtTwoComplex = invSqrtTwoComplex := by
  unfold invSqrtTwoComplex; exact Complex.conj_ofReal _

def cayleyCoeffFirstDiagonal (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then invSqrtTwoComplex else if r + k < i.val then -invSqrtTwoComplex else 1

def cayleyCoeffSecondDiagonal (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then invSqrtTwoComplex else if r + k < i.val then invSqrtTwoComplex else 0

def obj_PU (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  (if j = i then cayleyCoeffFirstDiagonal k r i else 0) + (if i = sig k r j then cayleyCoeffSecondDiagonal k r i else 0)

lemma obj_PU_star (k r : ℕ) (i j : Fin (2 * r + k + 1)) : star (obj_PU k r i j) = obj_PU k r i j := by
  unfold obj_PU cayleyCoeffFirstDiagonal cayleyCoeffSecondDiagonal
  split_ifs <;> simp [obj_s_star]

lemma obj_PJP_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ((obj_PU k r)ᴴ * Formalism.REAL.Jm (epsK k r) * obj_PU k r) i j = Hpk k r i j := by
  have hJ : Formalism.REAL.Jm (epsK k r) = diagonal (dK k r) := rfl
  have hs := obj_s_sq
  rw [hJ, mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, obj_PU_star]
  unfold obj_PU
  simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Hpk_eq]
  have hi := i.isLt
  have hs' := sig_val k r i
  by_cases hji : j = i
  · subst hji
    simp only [Fin.ext_iff]
    simp only [cayleyCoeffFirstDiagonal, cayleyCoeffSecondDiagonal, dK, epsK, sgn, decide_eq_true_eq]
    split_ifs at * <;> first | (exfalso; omega) | (linear_combination (0 : ℂ) * hs) | (linear_combination (2 : ℂ) * hs) | (linear_combination hs) | (linear_combination (-2 : ℂ) * hs) | (linear_combination (-1 : ℂ) * hs) | (norm_num; done)
  · by_cases hjs : j = sig k r i
    · subst hjs
      simp only [sig_sig]
      have hji' : ¬ (sig k r i).val = i.val := fun h => hji (Fin.ext h)
      simp only [Fin.ext_iff]
      simp only [cayleyCoeffFirstDiagonal, cayleyCoeffSecondDiagonal, dK, epsK, sgn, decide_eq_true_eq]
      split_ifs at * <;> first | (exfalso; omega) | (linear_combination (0 : ℂ) * hs) | (linear_combination (2 : ℂ) * hs) | (linear_combination hs) | (linear_combination (-2 : ℂ) * hs) | (linear_combination (-1 : ℂ) * hs) | (norm_num; done)
    · have h1 : ¬ i = j := fun h => hji h.symm
      have h2 : ¬ i = sig k r j := fun h => hjs ((eq_sig_iff k r i j).1 h)
      have h3 : ¬ sig k r j = sig k r i := fun h => hji ((sig_inj k r j i).1 h)
      rw [if_neg h1, if_neg hjs, if_neg h2, if_neg h3, if_neg hjs]
      norm_num

lemma obj_PP_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ((obj_PU k r)ᴴ * obj_PU k r) i j = (1 : Matrix _ _ ℂ) i j := by
  have hs := obj_s_sq
  rw [mul_apply]
  simp only [conjTranspose_apply, obj_PU_star]
  unfold obj_PU
  simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [one_apply]
  have hi := i.isLt
  have hs' := sig_val k r i
  by_cases hji : j = i
  · subst hji
    simp only [Fin.ext_iff]
    simp only [cayleyCoeffFirstDiagonal, cayleyCoeffSecondDiagonal]
    split_ifs at * <;> first | (exfalso; omega) | (linear_combination (0 : ℂ) * hs) | (linear_combination (2 : ℂ) * hs) | (linear_combination hs) | (linear_combination (-2 : ℂ) * hs) | (linear_combination (-1 : ℂ) * hs) | (norm_num; done)
  · by_cases hjs : j = sig k r i
    · subst hjs
      simp only [sig_sig]
      have hji' : ¬ (sig k r i).val = i.val := fun h => hji (Fin.ext h)
      simp only [Fin.ext_iff]
      simp only [cayleyCoeffFirstDiagonal, cayleyCoeffSecondDiagonal]
      split_ifs at * <;> first | (exfalso; omega) | (linear_combination (0 : ℂ) * hs) | (linear_combination (2 : ℂ) * hs) | (linear_combination hs) | (linear_combination (-2 : ℂ) * hs) | (linear_combination (-1 : ℂ) * hs) | (norm_num; done)
    · have h1 : ¬ i = j := fun h => hji h.symm
      have h2 : ¬ i = sig k r j := fun h => hjs ((eq_sig_iff k r i j).1 h)
      have h3 : ¬ sig k r j = sig k r i := fun h => hji ((sig_inj k r j i).1 h)
      rw [if_neg h1, if_neg hjs, if_neg h2, if_neg h3, if_neg h1]
      norm_num

lemma obj_PU_cayley (k r : ℕ) : IsCayleyU k r (epsK k r) (obj_PU k r) := by
  have h1 : (obj_PU k r)ᴴ * obj_PU k r = 1 := by ext i j; exact obj_PP_apply k r i j
  have hu : obj_PU k r ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']; exact h1
  refine ⟨⟨?_, by ext i j; exact obj_PJP_apply k r i j⟩, hu⟩
  exact ⟨⟨obj_PU k r, (obj_PU k r)ᴴ, mul_eq_one_comm.1 h1, h1⟩, rfl⟩

theorem obj_cayleyU_of_card (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (hc : (Finset.univ.filter fun i => ε i = true).card = k + r) : ∃ P, IsCayleyU k r ε P := by
  classical
  have hK : (Finset.univ.filter fun i : Fin (2 * r + k + 1) => epsK k r i = true).card = k + r := by
    have hf : (Finset.univ.filter fun i : Fin (2 * r + k + 1) => epsK k r i = true) =
        Finset.univ.filter fun i : Fin (2 * r + k + 1) => (i : ℕ) < r + k := by
      ext i; simp [epsK]
    rw [hf, Fin.card_filter_val_lt]; omega
  have hcard : Fintype.card {i // epsK k r i = true} = Fintype.card {i // ε i = true} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, hK, hc]
  let e0 : {i // epsK k r i = true} ≃ {i // ε i = true} := Fintype.equivOfCardEq hcard
  let π : Equiv.Perm (Fin (2 * r + k + 1)) := e0.extendSubtype
  have hπ : ∀ l, ε (π l) = epsK k r l := by
    intro l
    by_cases hl : epsK k r l = true
    · rw [hl]; exact e0.extendSubtype_mem l hl
    · have := e0.extendSubtype_not_mem l hl
      simp only [Bool.not_eq_true] at this hl
      rw [hl]; exact this
  obtain ⟨⟨_, hP⟩, hU⟩ := obj_PU_cayley k r
  have hU' : (obj_PU k r)ᴴ * obj_PU k r = 1 := (Matrix.mem_unitaryGroup_iff').1 hU
  let P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j => obj_PU k r (π.symm i) j
  have hsum : ∀ (d : Fin (2 * r + k + 1) → ℂ) a b, (Pᴴ * diagonal d * P) a b =
      ((obj_PU k r)ᴴ * diagonal (fun l => d (π l)) * obj_PU k r) a b := by
    intro d a b
    rw [mul_apply, mul_apply]
    simp only [mul_diagonal, conjTranspose_apply]
    rw [← Equiv.sum_comp π]
    simp [P]
  have h1 : Pᴴ * P = 1 := by
    have := fun a b => hsum (fun _ => 1) a b
    ext a b
    have h2 := this a b
    simp only [Matrix.diagonal_one, Matrix.mul_one] at h2
    rw [h2, hU']
  refine ⟨P, ⟨⟨⟨P, Pᴴ, mul_eq_one_comm.1 h1, h1⟩, rfl⟩, ?_⟩, (Matrix.mem_unitaryGroup_iff').2 h1⟩
  ext a b
  have hJ : Formalism.REAL.Jm ε = diagonal (fun a => if ε a then (1 : ℂ) else -1) := rfl
  rw [hJ, hsum, ← hP]
  have hJ' : Formalism.REAL.Jm (epsK k r) = diagonal (fun l => if ε (π l) then (1 : ℂ) else -1) := by
    show diagonal _ = _
    congr 1; funext l; rw [hπ]
  rw [hJ']

lemma obj_count (k r : ℕ) (hk : 1 ≤ k) :
    ((Finset.range (2 * r + k + 1)).filter fun i => i < k - 1 ∨ (i - (k - 1)) % 2 = 0).card = k + r := by
  induction r with
  | zero =>
    have : ((Finset.range (2 * 0 + k + 1)).filter fun i => i < k - 1 ∨ (i - (k - 1)) % 2 = 0) = Finset.range k := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this]; simp
  | succ r ih =>
    have e : 2 * (r + 1) + k + 1 = (2 * r + k + 1) + 1 + 1 := by ring
    rw [e, Finset.range_add_one, Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
      if_neg (by omega), if_pos (by omega), Finset.card_insert_of_notMem (by simp), ih]
    ring

lemma obj_card_fin (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter fun i : Fin n => p i.val).card = ((Finset.range n).filter p).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if p i then 1 else 0) n

theorem obj_epsSH_card (R : Formalism.BasicNotions.Ranks) :
    (Finset.univ.filter fun i => epsSH R i = true).card = R.k + R.rS := by
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  rw [← obj_count R.k R.rS hk, ← obj_card_fin]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, epsSH, epsS, Fin.val_cast]
  split_ifs with h <;> simp [h]

theorem obj_cayleyU_rows (D : Formalism.BasicNotions.D7) : ∃ P, IsCayleyU D.R.k D.R.rS (epsSH D.R) P :=
  obj_cayleyU_of_card _ _ _ (obj_epsSH_card D.R)

lemma obj_lamSH_lo (R : Formalism.BasicNotions.Ranks) (P : Formalism.BasicNotions.HCParam R) (i : Fin (2 * R.rS + R.k + 1)) (h : i.val < R.k - 1) :
    lamSH R P i = (P.v ⟨i.val, h⟩ : ℝ) := by
  unfold lamSH lamS; simp only [Fin.val_cast]; rw [dif_pos h]

lemma obj_lamSH_hi (R : Formalism.BasicNotions.Ranks) (P : Formalism.BasicNotions.HCParam R) (i : Fin (2 * R.rS + R.k + 1)) (h : ¬ i.val < R.k - 1)
    (h' : i.val - (R.k - 1) < R.m) : lamSH R P i = -(P.b ⟨i.val - (R.k - 1), h'⟩ : ℝ) := by
  unfold lamSH lamS; simp only [Fin.val_cast]; rw [dif_neg h, dif_pos h']

lemma obj_m_eq (R : Formalism.BasicNotions.Ranks) : R.m = 2 * R.rS + 2 := by
  obtain ⟨t, ht⟩ := R.m_even
  have h2 := R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.rS]; omega

theorem obj_isHCParam_lamSH (R : Formalism.BasicNotions.Ranks) (P : Formalism.BasicNotions.HCParam R) : IsHCParam (lamSH R P) := by
  have hm := obj_m_eq R
  have hk3 := R.m_add_three_le_k
  refine ⟨?_, ?_⟩
  · rw [Fin.strictAnti_iff_succ_lt]
    intro i
    have hi := i.isLt
    by_cases h1 : i.val + 1 < R.k - 1
    · rw [obj_lamSH_lo R P i.succ (by simpa using h1), obj_lamSH_lo R P i.castSucc (by simp; omega)]
      have a := P.u_gt_v ⟨i.val + 1, h1⟩
      have b := P.v_gt_u ⟨i.val, by omega⟩
      have c := lt_trans a b
      simp only [Fin.val_succ, Fin.val_castSucc]
      exact_mod_cast c
    · by_cases h2 : i.val < R.k - 1
      · have e : i.val + 1 = R.k - 1 := by omega
        rw [obj_lamSH_hi R P i.succ (by simpa using h1) (by simp; omega),
          obj_lamSH_lo R P i.castSucc (by simpa using h2)]
        have a := P.u_last_gt (by omega) (by omega)
        have b := P.v_gt_u ⟨i.val, h2⟩
        have e1 : (⟨i.val + 1, by omega⟩ : Fin R.k) = ⟨R.k - 1, by omega⟩ := Fin.ext e
        rw [e1] at b
        have c := lt_trans a b
        have e2 : (⟨(i.succ).val - (R.k - 1), by simp; omega⟩ : Fin R.m) = ⟨0, by omega⟩ := by
          apply Fin.ext; simp; omega
        rw [e2]
        simp only [Fin.val_castSucc]
        exact_mod_cast c
      · rw [obj_lamSH_hi R P i.succ (by simpa using h1) (by simp; omega),
          obj_lamSH_hi R P i.castSucc (by simpa using h2) (by simp; omega)]
        have hj : i.val - (R.k - 1) < R.m := by omega
        have hj1 : i.val - (R.k - 1) + 1 < R.m := by omega
        have a := P.gap_be ⟨i.val - (R.k - 1), hj⟩
        have b := P.gap_eb ⟨i.val - (R.k - 1), hj⟩ hj1
        have e2 : (⟨(i.succ).val - (R.k - 1), by simp; omega⟩ : Fin R.m) = ⟨i.val - (R.k - 1) + 1, hj1⟩ := by
          apply Fin.ext; simp; omega
        rw [e2]
        simp only [Fin.val_castSucc]
        have t0 : (0 : ℚ) ≤ (R.t : ℚ) := Nat.cast_nonneg _
        have c : P.b ⟨i.val - (R.k - 1), hj⟩ < P.b ⟨i.val - (R.k - 1) + 1, hj1⟩ := by linarith
        have c' : (P.b ⟨i.val - (R.k - 1), hj⟩ : ℝ) < (P.b ⟨i.val - (R.k - 1) + 1, hj1⟩ : ℝ) := by exact_mod_cast c
        linarith
  · intro a
    obtain ⟨q, hq⟩ := R.k_even
    have hn : (((2 * R.rS + R.k + 1 : ℕ) : ℝ) - 1) / 2 = ((R.rS + q : ℕ) : ℝ) := by
      rw [hq]; push_cast; ring
    have ha := a.isLt
    by_cases h : a.val < R.k - 1
    · obtain ⟨z, hz⟩ := P.v_int ⟨a.val, h⟩
      refine ⟨z - (R.rS + q : ℕ), ?_⟩
      rw [obj_lamSH_lo R P a h, hn, hz]; push_cast; ring
    · obtain ⟨z, hz⟩ := P.b_int ⟨a.val - (R.k - 1), by omega⟩
      refine ⟨-z - (R.rS + q : ℕ), ?_⟩
      rw [obj_lamSH_hi R P a h (by omega), hn, hz]; push_cast; ring

theorem obj_isHCParam_u (R : Formalism.BasicNotions.Ranks) (P : Formalism.BasicNotions.HCParam R) : IsHCParam (fun i => ((P.u i : ℚ) : ℝ)) := by
  have hk3 := R.m_add_three_le_k
  refine ⟨?_, ?_⟩
  · have key : ∀ (i : ℕ) (h : i + 1 < R.k), P.u ⟨i + 1, h⟩ < P.u ⟨i, by omega⟩ := by
      intro i h
      exact lt_trans (P.v_gt_u ⟨i, by omega⟩) (P.u_gt_v ⟨i, by omega⟩)
    have anti : ∀ (d i : ℕ) (h : i + d + 1 < R.k), P.u ⟨i + d + 1, h⟩ < P.u ⟨i, by omega⟩ := by
      intro d
      induction d with
      | zero => intro i h; exact key i h
      | succ d ih => intro i h; exact lt_trans (key (i + d + 1) h) (ih i (by omega))
    intro a b hab
    have hab' : a.val < b.val := hab
    have := anti (b.val - a.val - 1) a.val (by have := b.isLt; omega)
    have e : (⟨a.val + (b.val - a.val - 1) + 1, by have := b.isLt; omega⟩ : Fin R.k) = b := by
      apply Fin.ext; simp; omega
    rw [e] at this
    show ((P.u b : ℚ) : ℝ) < ((P.u a : ℚ) : ℝ)
    exact_mod_cast this
  · intro a
    obtain ⟨q, hq⟩ := R.k_even
    obtain ⟨z, hz⟩ := P.u_half a
    refine ⟨z + 1 - q, ?_⟩
    show ((P.u a : ℚ) : ℝ) - ((R.k : ℝ) - 1) / 2 = _
    rw [hz, hq]; push_cast; ring

theorem obj_interlace (R : Formalism.BasicNotions.Ranks) (P : Formalism.BasicNotions.HCParam R) :
    InterlaceS (by omega : R.k ≤ 2 * R.rS + R.k + 1) (fun i => ((P.u i : ℚ) : ℝ)) (lamSH R P) := by
  have hm := obj_m_eq R
  have hk3 := R.m_add_three_le_k
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [obj_lamSH_lo R P ⟨i, by omega⟩ (by show i < R.k - 1; omega)]
    have a := P.u_gt_v ⟨i, by omega⟩
    have b := P.v_gt_u ⟨i, by omega⟩
    refine ⟨?_, ?_⟩
    · beta_reduce; exact_mod_cast a
    · beta_reduce; exact_mod_cast b
  · intro h
    rw [obj_lamSH_hi R P ⟨R.k - 1, by omega⟩ (by show ¬ R.k - 1 < R.k - 1; omega) (by show R.k - 1 - (R.k - 1) < R.m; omega)]
    have a := P.u_last_gt h (by omega)
    have e2 : (⟨R.k - 1 - (R.k - 1), by omega⟩ : Fin R.m) = ⟨0, by omega⟩ := by apply Fin.ext; simp
    rw [e2]
    beta_reduce
    exact_mod_cast a

open Formalism.MainNotions.CayleySignature in

theorem exists_isCayleyU_eps48 (k r : ℕ) (hk : 1 ≤ k) : ∃ P, IsCayleyU k r (eps48 k r) P := by
  apply obj_cayleyU_of_card
  have e : (Finset.univ.filter fun i => eps48 k r i = true) =
      Finset.univ.filter (fun i : Fin (2 * r + k + 1) => i.val < k - 1 ∨ (i.val - (k - 1)) % 2 = 0) := by
    apply Finset.filter_congr
    intro i _
    unfold eps48
    by_cases h : i.val < k - 1 <;> simp [h]
  rw [e, obj_card_fin (2 * r + k + 1) (fun i => i < k - 1 ∨ (i - (k - 1)) % 2 = 0), obj_count k r hk]

def thresholdForNumericSetting (k r : ℕ) : ℕ := 2 * Formalism.MainNotions.CayleySignature.rk48 k r + 1801

def gapScaleForNumericSetting (k r : ℕ) (C : ℝ) : ℕ :=
  ⌈|C| * (Formalism.MainNotions.CayleySignature.rk48 k r : ℝ) ^ 3⌉₊ + 2 * (Formalism.MainNotions.CayleySignature.rk48 k r + (2 * r + 2) * thresholdForNumericSetting k r) ^ 3 + thresholdForNumericSetting k r + 4

def halfIntegerHighParameter (k : ℕ) : Fin k → ℝ := fun i => (k : ℝ) - (i.val : ℝ) + 1 / 2
def integerHighParameter (k : ℕ) : Fin (k - 1) → ℝ := fun i => (k : ℝ) - (i.val : ℝ)
def evenlySpacedLowParameter (k r : ℕ) (C : ℝ) : Fin (2 * r + 2) → ℝ := fun j => (j.val : ℝ) * (gapScaleForNumericSetting k r C : ℝ)

lemma lambda_numeric_setting_eq (k r : ℕ) (C : ℝ) (i : Fin (2 * r + k + 1)) :
    Formalism.MainNotions.CayleySignature.lam48 k r (integerHighParameter k) (evenlySpacedLowParameter k r C) i =
      if i.val < k - 1 then (k : ℝ) - (i.val : ℝ) else -(((i.val - (k - 1) : ℕ) : ℝ) * (gapScaleForNumericSetting k r C : ℝ)) := by
  unfold Formalism.MainNotions.CayleySignature.lam48 integerHighParameter evenlySpacedLowParameter
  split_ifs <;> rfl

lemma gap_scale_numeric_setting_pos (k r : ℕ) (C : ℝ) : (0 : ℝ) < (gapScaleForNumericSetting k r C : ℝ) := by
  have : 0 < gapScaleForNumericSetting k r C := by unfold gapScaleForNumericSetting; omega
  exact_mod_cast this

open Formalism.MainNotions.CayleySignature in

theorem numeric_setting_with_gap_satisfiable (k r : ℕ) (hk : 1 ≤ k) (he : Even k) (C : ℝ) :
    ∃ z c u v b, RealPlaceNumericalSetting k r z c u v b ∧ GapC C k r b := by
  have hG := gap_scale_numeric_setting_pos k r C
  obtain ⟨q, hq⟩ := he
  have hgap : ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      evenlySpacedLowParameter k r C ⟨j.val + 1, hj⟩ - evenlySpacedLowParameter k r C j = (gapScaleForNumericSetting k r C : ℝ) := by
    intro j hj; unfold evenlySpacedLowParameter; push_cast; ring
  have hGc : (gapScaleForNumericSetting k r C : ℝ) = (⌈|C| * (rk48 k r : ℝ) ^ 3⌉₊ : ℝ) +
      2 * ((rk48 k r + (2 * r + 2) * thresholdForNumericSetting k r : ℕ) : ℝ) ^ 3 + (thresholdForNumericSetting k r : ℝ) + 4 := by
    unfold gapScaleForNumericSetting; push_cast; ring
  have hceil : |C| * (rk48 k r : ℝ) ^ 3 ≤ (⌈|C| * (rk48 k r : ℝ) ^ 3⌉₊ : ℝ) := Nat.le_ceil _
  have hceil0 : (0 : ℝ) ≤ (⌈|C| * (rk48 k r : ℝ) ^ 3⌉₊ : ℝ) := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ 2 * ((rk48 k r + (2 * r + 2) * thresholdForNumericSetting k r : ℕ) : ℝ) ^ 3 := by positivity
  have ht0 : (0 : ℝ) ≤ (thresholdForNumericSetting k r : ℝ) := Nat.cast_nonneg _
  refine ⟨bvec (wI k r (Fin.last k)), fun _ => 1, halfIntegerHighParameter k, integerHighParameter k, evenlySpacedLowParameter k r C,
    ⟨hk, ⟨q, hq⟩, ?_, ?_, fun _ => one_ne_zero, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  ·
    intro i hi
    unfold bvec wI
    rw [Pi.single_apply, if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  ·
    unfold Tz
    rw [herm_bvec, Hpk_eq, if_pos, sgn, if_pos]
    · norm_num
    · simp [wI]
    · rw [sig_mid] <;> simp [wI]
  ·
    intro a b hab
    have : (a.val : ℝ) < (b.val : ℝ) := by exact_mod_cast hab
    unfold halfIntegerHighParameter; linarith
  · intro a
    refine ⟨(q : ℤ) - a.val + 1, ?_⟩
    have hkq : (k : ℝ) = (q : ℝ) + q := by exact_mod_cast hq
    unfold halfIntegerHighParameter; push_cast; linear_combination (1 / 2 : ℝ) * hkq
  ·
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    have hi := i.isLt
    rw [lambda_numeric_setting_eq, lambda_numeric_setting_eq]
    simp only [Fin.val_succ, Fin.val_castSucc]
    split_ifs with h1 h2 h2
    · push_cast; linarith
    · omega
    · have e : i.val + 1 - (k - 1) = 0 := by omega
      rw [e]
      have : (i.val : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : i.val < k)
      simp only [Nat.cast_zero, zero_mul, neg_zero]; linarith
    · have e : i.val + 1 - (k - 1) = (i.val - (k - 1)) + 1 := by omega
      rw [e]; push_cast
      have : (((i.val - (k - 1) : ℕ) : ℝ) + 1) * (gapScaleForNumericSetting k r C : ℝ) =
        ((i.val - (k - 1) : ℕ) : ℝ) * (gapScaleForNumericSetting k r C : ℝ) + (gapScaleForNumericSetting k r C : ℝ) := by ring
      linarith
  · intro a
    have hn : (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 = ((r + q : ℕ) : ℝ) := by rw [hq]; push_cast; ring
    rw [lambda_numeric_setting_eq, hn]
    split_ifs with h
    · refine ⟨(k : ℤ) - a.val - (r + q : ℕ), ?_⟩; push_cast; ring
    · refine ⟨-(((a.val - (k - 1) : ℕ) : ℤ) * (gapScaleForNumericSetting k r C : ℤ)) - (r + q : ℕ), ?_⟩; push_cast; ring
  ·
    intro i
    unfold halfIntegerHighParameter integerHighParameter
    refine ⟨by simp only []; linarith, by simp only []; push_cast; linarith⟩
  · intro h
    unfold halfIntegerHighParameter evenlySpacedLowParameter
    have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk]; simp
    simp only [this]
    push_cast; linarith
  ·
    intro i s
    rw [lambda_numeric_setting_eq]
    unfold halfIntegerHighParameter
    split_ifs with h
    · refine ⟨(s.val : ℤ) - i.val, ?_⟩; push_cast; ring
    · refine ⟨(k : ℤ) - i.val + ((s.val - (k - 1) : ℕ) : ℤ) * (gapScaleForNumericSetting k r C : ℤ), ?_⟩; push_cast; ring
  ·
    refine ⟨thresholdForNumericSetting k r, ⟨rk48 k r + 900, by unfold thresholdForNumericSetting; ring⟩, by unfold thresholdForNumericSetting; omega, by unfold thresholdForNumericSetting; omega, ?_⟩
    intro j hj
    rw [hgap j hj, hGc]; linarith
  · intro j hj
    rw [hgap j hj, hGc]
    have : C * (rk48 k r : ℝ) ^ 3 ≤ |C| * (rk48 k r : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    linarith

end obj

end Formalism.MainNotions.S.Inh
