import Formalism.SharpRestriction.LevelLetterCocycles.AdmBoundsBOfAdm
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.InvSubOneSqLeInv

noncomputable section

open Classical

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.SetupA

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

section Num

def SgN (l h w S η : ℕ) : ℝ :=
  (h : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + S + η) / l + Real.logb l (2 * (h : ℝ)) + 1

def cW (l H : ℕ) : ℕ := ⌈1 + Real.logb l ((H : ℝ) + 1)⌉₊

theorem tsum_three (l : ℕ) (hl : 11 ≤ l) (f : ℕ → ℝ) (x₀ x₁ X : ℝ) (hf : ∀ a, 0 ≤ f a)
    (h0 : f 0 ≤ x₀) (h1 : f 1 ≤ x₁) (h2 : ∀ a, 2 ≤ a → f a ≤ X) :
    ∑' a : ℕ, f a * ((l : ℝ) - 1) ^ (-(a : ℤ)) ≤
      x₀ + x₁ / ((l : ℝ) - 1) + X / (((l : ℝ) - 1) * ((l : ℝ) - 2)) := by
  have ht : (11:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((l:ℝ) - 1)⁻¹ := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact inv_nonneg.mpr (by linarith)
  have hqm : q * ((l:ℝ) - 1) = 1 := by rw [hq]; exact inv_mul_cancel₀ (by linarith)
  have hq1 : q < 1 := by nlinarith
  have hterm : ∀ a : ℕ, ((l:ℝ) - 1) ^ (-(a:ℤ)) = q ^ a := by
    intro a; rw [hq, inv_pow, zpow_neg, zpow_natCast]
  simp_rw [hterm]
  have hX : 0 ≤ X := le_trans (hf 2) (h2 2 le_rfl)
  have hB : ∀ a, f a ≤ max (f 0) (max (f 1) X) := by
    intro a
    rcases a with _ | _ | a
    · exact le_max_left _ _
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (h2 _ (by omega)) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hsum : Summable (fun a : ℕ => f a * q ^ a) :=
    Summable.of_nonneg_of_le (fun a => mul_nonneg (hf a) (pow_nonneg hq0 a))
      (fun a => mul_le_mul_of_nonneg_right (hB a) (pow_nonneg hq0 a))
      ((summable_geometric_of_lt_one hq0 hq1).mul_left _)
  have hsplit := Summable.sum_add_tsum_nat_add 2 hsum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    mul_one] at hsplit
  have htail : ∑' i : ℕ, f (i + 2) * q ^ (i + 2) ≤ X * q ^ 2 * (1 - q)⁻¹ := by
    have hs2 : Summable (fun i : ℕ => X * q ^ 2 * q ^ i) :=
      (summable_geometric_of_lt_one hq0 hq1).mul_left _
    have hs1 : Summable (fun i : ℕ => f (i + 2) * q ^ (i + 2)) :=
      (summable_nat_add_iff 2).mpr hsum
    calc ∑' i : ℕ, f (i + 2) * q ^ (i + 2) ≤ ∑' i : ℕ, X * q ^ 2 * q ^ i := by
          refine Summable.tsum_le_tsum (fun i => ?_) hs1 hs2
          calc f (i + 2) * q ^ (i + 2) ≤ X * q ^ (i + 2) :=
                mul_le_mul_of_nonneg_right (h2 _ (by omega)) (pow_nonneg hq0 _)
            _ = X * q ^ 2 * q ^ i := by ring
      _ = X * q ^ 2 * (1 - q)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have e1 : x₁ / ((l:ℝ) - 1) = x₁ * q := by rw [hq, div_eq_mul_inv]
  have e2 : X * q ^ 2 * (1 - q)⁻¹ = X / (((l:ℝ) - 1) * ((l:ℝ) - 2)) := by
    have h1' : (l:ℝ) - 1 ≠ 0 := by linarith
    have h2' : (l:ℝ) - 2 ≠ 0 := by linarith
    have h3' : (l:ℝ) - 1 - 1 ≠ 0 := by linarith
    rw [hq]; field_simp; ring
  have hx1 : f 1 * q ≤ x₁ * q := mul_le_mul_of_nonneg_right h1 hq0
  rw [e1, ← e2, ← hsplit]
  linarith

theorem cW_le (l : ℕ) (hl : 11 ≤ l) (h η H : ℕ) (hη : η + 1 ≤ h) (hH : H ≤ h + η) :
    (cW l H : ℝ) ≤ 2 + Real.logb l (2 * (h : ℝ)) := by
  have ht : (11:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl
  have hl' : (1:ℝ) < l := by linarith
  have hH0 : (0:ℝ) ≤ H := Nat.cast_nonneg H
  have hlog0 : 0 ≤ Real.logb l ((H:ℝ) + 1) := Real.logb_nonneg hl' (by linarith)
  have hle : (H:ℝ) + 1 ≤ 2 * (h:ℝ) := by
    have : H + 1 ≤ 2 * h := by omega
    exact_mod_cast this
  have hmono := Real.logb_le_logb_of_le hl' (by linarith) hle
  have hceil := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 1 + Real.logb l ((H:ℝ) + 1) by linarith)
  unfold cW
  linarith

private lemma div_le_div_of_mul_le_mul_of_pos {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    a / b ≤ c / d := by
  have hb' : b ≠ 0 := hb.ne'
  have hd' : d ≠ 0 := hd.ne'
  have hbd : 0 < b * d := mul_pos hb hd
  have e1 : a / b = (a * d) * (b * d)⁻¹ := by field_simp <;> ring
  have e2 : c / d = (c * b) * (b * d)⁻¹ := by field_simp <;> ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hbd.le)

theorem rr_le (l : ℕ) (hl : 11 ≤ l) (h w S η H H₁ : ℕ) (hη : η + 1 ≤ h)
    (hH : H ≤ h + η) (hH₁ : H₁ ≤ w + S + η) (s r : ℝ)
    (hs : s ≤ ((H₁ : ℝ) + cW l H + 3) + ((H : ℝ) + cW l H + 3) / ((l : ℝ) - 2))
    (hr : r ≤ s * l / ((l : ℝ) - 1) ^ 2 + cW l H) :
    r ≤ 2 * ((w : ℝ) + S + η) / l + 2 * (h : ℝ) / (l : ℝ) ^ 2 + 2 * Real.logb l (2 * (h : ℝ)) + 3 ∧
    2 * ((w : ℝ) + S + η) / l + 2 * (h : ℝ) / (l : ℝ) ^ 2 + 2 * Real.logb l (2 * (h : ℝ)) + 3 ≤
      3 * SgN l h w S η := by
  have ht : (11:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl
  have hc := cW_le l hl h η H hη hH
  have hc0 : (0:ℝ) ≤ (cW l H : ℝ) := Nat.cast_nonneg _
  have hl1 : (1:ℝ) < l := by linarith
  have hh1 : (1:ℝ) ≤ 2 * (h:ℝ) := by
    have : 1 ≤ h := by omega
    have : (1:ℝ) ≤ h := by exact_mod_cast this
    linarith
  have hL0 : 0 ≤ Real.logb l (2 * (h:ℝ)) := Real.logb_nonneg hl1 hh1
  have hA : (H₁:ℝ) ≤ (w:ℝ) + S + η := by exact_mod_cast hH₁
  have hHh : (H:ℝ) ≤ (h:ℝ) + η := by exact_mod_cast hH
  have hw0 : (0:ℝ) ≤ w := Nat.cast_nonneg w
  have hS0 : (0:ℝ) ≤ S := Nat.cast_nonneg S
  have hη0 : (0:ℝ) ≤ η := Nat.cast_nonneg η
  have hh0 : (0:ℝ) ≤ h := Nat.cast_nonneg h
  have hA0 : (0:ℝ) ≤ (w:ℝ) + S + η := by linarith
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (l:ℝ) / ((l:ℝ) - 1) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (l:ℝ) / (((l:ℝ) - 1) ^ 2 * ((l:ℝ) - 2)) := ⟨_, rfl⟩
  have h1' : (l:ℝ) - 1 ≠ 0 := by linarith
  have h2' : (l:ℝ) - 2 ≠ 0 := by linarith
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hQ0 : 0 ≤ Q := by
    rw [hQ]; exact div_nonneg (by linarith) (mul_nonneg (sq_nonneg _) (by linarith))
  have hPQe : P + Q = (l:ℝ) / (((l:ℝ) - 1) * ((l:ℝ) - 2)) := by
    rw [hP, hQ]; field_simp; ring
  have hpos : (0:ℝ) < ((l:ℝ) - 1) * ((l:ℝ) - 2) := mul_pos (by linarith) (by linarith)
  have hPQ2 : P + Q ≤ 2 / (l:ℝ) := by
    rw [hPQe]
    exact div_le_div_of_mul_le_mul_of_pos hpos (by linarith) (by nlinarith)
  have hPQ8 : P + Q ≤ 1 / 8 := by
    rw [hPQe]
    exact div_le_div_of_mul_le_mul_of_pos hpos (by norm_num)
      (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (l:ℝ) - 11) (by linarith : (0:ℝ) ≤ (l:ℝ))])
  have hQ2 : Q ≤ 2 / (l:ℝ) ^ 2 := by
    have hpos3 : (0:ℝ) < ((l:ℝ) - 1) ^ 2 * ((l:ℝ) - 2) :=
      mul_pos (pow_pos (by linarith) 2) (by linarith)
    rw [hQ]
    exact div_le_div_of_mul_le_mul_of_pos hpos3 (by positivity)
      (by nlinarith [mul_nonneg (sq_nonneg (l:ℝ)) (by linarith : (0:ℝ) ≤ (l:ℝ) - 11)])
  have hrP : r ≤ s * P + cW l H := by
    have : s * l / ((l:ℝ) - 1) ^ 2 = s * P := by rw [hP]; ring
    linarith
  have hs' : s ≤ ((w:ℝ) + S + η + cW l H + 3) + ((h:ℝ) + η + cW l H + 3) / ((l:ℝ) - 2) := by
    have : ((H:ℝ) + cW l H + 3) / ((l:ℝ) - 2) ≤ ((h:ℝ) + η + cW l H + 3) / ((l:ℝ) - 2) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hsP : s * P ≤ (((w:ℝ) + S + η + cW l H + 3) + ((h:ℝ) + η + cW l H + 3) / ((l:ℝ) - 2)) * P :=
    mul_le_mul_of_nonneg_right hs' hP0
  have hexp : (((w:ℝ) + S + η + cW l H + 3) + ((h:ℝ) + η + cW l H + 3) / ((l:ℝ) - 2)) * P =
      ((w:ℝ) + S + η) * P + (η:ℝ) * Q + (h:ℝ) * Q + ((cW l H : ℝ) + 3) * (P + Q) := by
    rw [hP, hQ]; field_simp; ring
  have hb1 : (η:ℝ) * Q ≤ ((w:ℝ) + S + η) * Q := mul_le_mul_of_nonneg_right (by linarith) hQ0
  have hb2 : ((w:ℝ) + S + η) * (P + Q) ≤ ((w:ℝ) + S + η) * (2 / (l:ℝ)) :=
    mul_le_mul_of_nonneg_left hPQ2 hA0
  have hb3 : (h:ℝ) * Q ≤ (h:ℝ) * (2 / (l:ℝ) ^ 2) := mul_le_mul_of_nonneg_left hQ2 hh0
  have hb4 : ((cW l H : ℝ) + 3) * (P + Q) ≤ ((cW l H : ℝ) + 3) * (1 / 8) :=
    mul_le_mul_of_nonneg_left hPQ8 (by linarith)
  have key : r ≤ 2 * ((w:ℝ) + S + η) / l + 2 * (h:ℝ) / (l:ℝ) ^ 2 + 2 * Real.logb l (2 * (h:ℝ)) + 3 := by
    have e1 : ((w:ℝ) + S + η) * (2 / (l:ℝ)) = 2 * ((w:ℝ) + S + η) / l := by ring
    have e2 : (h:ℝ) * (2 / (l:ℝ) ^ 2) = 2 * (h:ℝ) / (l:ℝ) ^ 2 := by ring
    linarith
  refine ⟨key, ?_⟩
  unfold SgN
  have q1 : 0 ≤ (h:ℝ) / (l:ℝ) ^ 2 := by positivity
  have q2 : 0 ≤ ((w:ℝ) + S + η) / l := by positivity
  have e3 : 2 * ((w:ℝ) + S + η) / l = 2 * (((w:ℝ) + S + η) / l) := by ring
  have e4 : 2 * (h:ℝ) / (l:ℝ) ^ 2 = 2 * ((h:ℝ) / (l:ℝ) ^ 2) := by ring
  rw [e3, e4]
  linarith

theorem sig_le (l : ℕ) (hl : 11 ≤ l) (h w S η : ℕ) (h1 : 1 ≤ h) (hG : w + S ≤ h) :
    (⌈((2 * (w + S) : ℕ) + ((2 * h / (l - 1) + 1 : ℕ) : ℝ)) * l / ((l : ℝ) - 1) ^ 2 + 1⌉₊ : ℝ) ≤
      3 * SgN l h w S η := by
  have ht : (11:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl
  have hl1 : (1:ℝ) < l := by linarith
  have hh : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast h1
  have hG' : (w:ℝ) + S ≤ h := by exact_mod_cast hG
  have hw0 : (0:ℝ) ≤ w := Nat.cast_nonneg w
  have hS0 : (0:ℝ) ≤ S := Nat.cast_nonneg S
  have hη0 : (0:ℝ) ≤ η := Nat.cast_nonneg η
  have hL0 : 0 ≤ Real.logb l (2 * (h:ℝ)) := Real.logb_nonneg hl1 (by linarith)
  have hM : ((2 * h / (l - 1) + 1 : ℕ) : ℝ) ≤ 2 * (h:ℝ) / ((l:ℝ) - 1) + 1 := by
    have e0 : ((l - 1 : ℕ) : ℝ) = (l:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have hdiv : ((2 * h / (l - 1) : ℕ) : ℝ) ≤ ((2 * h : ℕ) : ℝ) / ((l - 1 : ℕ) : ℝ) :=
      Nat.cast_div_le
    rw [e0] at hdiv
    rw [Nat.cast_add, Nat.cast_one]
    have : ((2 * h : ℕ) : ℝ) = 2 * (h:ℝ) := by push_cast; ring
    rw [this] at hdiv
    linarith
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ((2 * h / (l - 1) + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hMdef] at hM ⊢
  have hWS : ((2 * (w + S) : ℕ) : ℝ) = 2 * ((w:ℝ) + S) := by push_cast; ring
  rw [hWS]
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (l:ℝ) / ((l:ℝ) - 1) ^ 2 := ⟨_, rfl⟩
  have h1' : (l:ℝ) - 1 ≠ 0 := by linarith
  have hsq : (0:ℝ) < ((l:ℝ) - 1) ^ 2 := pow_pos (by linarith) 2
  have hP0 : 0 ≤ P := by rw [hP]; exact div_nonneg (by linarith) hsq.le
  have hM0 : 0 ≤ M := by rw [hMdef]; exact Nat.cast_nonneg _
  have ex : (2 * ((w:ℝ) + S) + M) * l / ((l:ℝ) - 1) ^ 2 + 1 = (2 * ((w:ℝ) + S) + M) * P + 1 := by
    rw [hP]; ring
  rw [ex]
  have hx0 : (0:ℝ) ≤ (2 * ((w:ℝ) + S) + M) * P + 1 := by positivity
  have hceil := Nat.ceil_lt_add_one hx0
  have hP2 : 2 * P ≤ 3 / (l:ℝ) := by
    rw [hP, show 2 * ((l:ℝ) / ((l:ℝ) - 1) ^ 2) = (2 * (l:ℝ)) / ((l:ℝ) - 1) ^ 2 by ring]
    exact div_le_div_of_mul_le_mul_of_pos hsq (by linarith) (by nlinarith)
  have hPh : 2 / ((l:ℝ) - 1) * P ≤ 3 / (l:ℝ) ^ 2 := by
    have hcu : (0:ℝ) < ((l:ℝ) - 1) ^ 3 := pow_pos (by linarith) 3
    rw [hP, show 2 / ((l:ℝ) - 1) * ((l:ℝ) / ((l:ℝ) - 1) ^ 2) = (2 * (l:ℝ)) / ((l:ℝ) - 1) ^ 3 by
      field_simp <;> ring]
    exact div_le_div_of_mul_le_mul_of_pos hcu (by positivity)
      (by nlinarith [mul_nonneg (sq_nonneg (l:ℝ)) (by linarith : (0:ℝ) ≤ (l:ℝ) - 11)])
  have hP1 : P ≤ 1 := by
    rw [hP]
    have hq := div_le_div_of_mul_le_mul_of_pos (a := (l:ℝ)) (c := 1) (d := 1) hsq one_pos (by nlinarith)
    rwa [div_one] at hq
  have hnum : (2 * ((w:ℝ) + S) + M) * P ≤ (2 * ((w:ℝ) + S) + 2 * (h:ℝ) / ((l:ℝ) - 1) + 1) * P :=
    mul_le_mul_of_nonneg_right (by linarith) hP0
  have hb1 : ((w:ℝ) + S) * (2 * P) ≤ ((w:ℝ) + S) * (3 / (l:ℝ)) :=
    mul_le_mul_of_nonneg_left hP2 (by linarith)
  have hb2 : (h:ℝ) * (2 / ((l:ℝ) - 1) * P) ≤ (h:ℝ) * (3 / (l:ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hPh (by linarith)
  have hexp : (2 * ((w:ℝ) + S) + 2 * (h:ℝ) / ((l:ℝ) - 1) + 1) * P =
      ((w:ℝ) + S) * (2 * P) + (h:ℝ) * (2 / ((l:ℝ) - 1) * P) + P := by ring
  have hη' : 0 ≤ (η:ℝ) / l := by positivity
  unfold SgN
  have e1 : ((w:ℝ) + S) * (3 / (l:ℝ)) = 3 * (((w:ℝ) + S) / l) := by ring
  have e2 : (h:ℝ) * (3 / (l:ℝ) ^ 2) = 3 * ((h:ℝ) / (l:ℝ) ^ 2) := by ring
  have e3 : ((w:ℝ) + S + η) / l = ((w:ℝ) + S) / l + (η:ℝ) / l := by ring
  rw [e3]
  linarith

end Num

section Comb

variable {n : ℕ} [NeZero n] (th : ZMod n → Prop)

def lenT (c : ZMod n) : ℕ := sInf {d : ℕ | 1 ≤ d ∧ ¬ th (c - (d : ZMod n) + 1)}

theorem lenT_spec (c : ZMod n) (hc : ¬ th (c + 1)) :
    1 ≤ lenT th c ∧ lenT th c ≤ n ∧ ¬ th (c - (lenT th c : ZMod n) + 1) ∧
      ∀ d : ℕ, 1 ≤ d → d < lenT th c → th (c - (d : ZMod n) + 1) := by
  have hn : (n : ZMod n) = 0 := by simp
  have hmem : n ∈ {d : ℕ | 1 ≤ d ∧ ¬ th (c - (d : ZMod n) + 1)} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨Nat.one_le_iff_ne_zero.mpr (NeZero.ne n), ?_⟩
    rw [hn, sub_zero]; exact hc
  have hs : 1 ≤ lenT th c ∧ ¬ th (c - (lenT th c : ZMod n) + 1) :=
    Nat.sInf_mem (s := {d : ℕ | 1 ≤ d ∧ ¬ th (c - (d : ZMod n) + 1)}) ⟨n, hmem⟩
  refine ⟨hs.1, Nat.sInf_le hmem, hs.2, ?_⟩
  intro d hd hdl
  by_contra hcon
  have hd' : d ∈ {d : ℕ | 1 ≤ d ∧ ¬ th (c - (d : ZMod n) + 1)} := by
    simp only [Set.mem_setOf_eq]; exact ⟨hd, hcon⟩
  exact absurd (Nat.sInf_le hd') (not_le.mpr hdl)

theorem sum_lenT (hne : ∃ i, ¬ th i) :
    ∑ c ∈ Finset.univ.filter (fun c => ¬ th (c + 1)), lenT th c = n := by
  obtain ⟨j, hj⟩ := hne
  let S : ZMod n → Set ℕ := fun i => {e : ℕ | ¬ th (i + (e : ZMod n) + 1)}
  have hE : ∀ i : ZMod n, (S i).Nonempty := by
    intro i
    refine ⟨(j - i - 1).val, ?_⟩
    show ¬ th (i + (((j - i - 1).val : ℕ) : ZMod n) + 1)
    rw [ZMod.natCast_zmod_val]
    have e0 : i + (j - i - 1) + 1 = j := by ring
    rw [e0]; exact hj
  let e : ZMod n → ℕ := fun i => sInf (S i)
  have he1 : ∀ i, ¬ th (i + (e i : ZMod n) + 1) := fun i => Nat.sInf_mem (hE i)
  have he3 : ∀ i (k : ℕ), ¬ th (i + (k : ZMod n) + 1) → e i ≤ k :=
    fun i k hk => Nat.sInf_le (s := S i) hk
  have he2 : ∀ i (k : ℕ), k < e i → th (i + (k : ZMod n) + 1) := by
    intro i k hk
    by_contra hc
    exact absurd (he3 i k hc) (not_le.mpr hk)
  have hκ : ∀ i ∈ (Finset.univ : Finset (ZMod n)),
      (fun i => i + (e i : ZMod n)) i ∈ Finset.univ.filter (fun c => ¬ th (c + 1)) := by
    intro i _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, he1 i⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hκ
  rw [Finset.card_univ, ZMod.card] at hcard
  refine (Finset.sum_congr rfl (fun c hc => ?_)).trans hcard.symm
  rw [Finset.mem_filter] at hc
  obtain ⟨hL1, hLn, hLf, hLt⟩ := lenT_spec th c hc.2
  have hfib : Finset.univ.filter (fun i => i + (e i : ZMod n) = c) =
      (Finset.range (lenT th c)).image (fun k : ℕ => c - (k : ZMod n)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hi
      refine ⟨e i, ?_, ?_⟩
      · by_contra hlt
        push_neg at hlt
        have h1 : e i - lenT th c < e i := by omega
        have h2 := he2 i _ h1
        have h3 : i + ((e i - lenT th c : ℕ) : ZMod n) + 1 = c - (lenT th c : ZMod n) + 1 := by
          rw [Nat.cast_sub hlt, ← hi]; ring
        rw [h3] at h2
        exact hLf h2
      · rw [← hi]; ring
    · rintro ⟨k, hk, rfl⟩
      have hek : e (c - (k : ZMod n)) = k := by
        apply le_antisymm
        · apply he3
          have e4 : c - (k : ZMod n) + (k : ZMod n) + 1 = c + 1 := by ring
          rw [e4]; exact hc.2
        · by_contra hlt
          push_neg at hlt
          apply he1 (c - (k : ZMod n))
          have hth := hLt (k - e (c - (k : ZMod n))) (by omega) (by omega)
          have e5 : c - (k : ZMod n) + ((e (c - (k : ZMod n)) : ℕ) : ZMod n) + 1 =
              c - ((k - e (c - (k : ZMod n)) : ℕ) : ZMod n) + 1 := by
            rw [Nat.cast_sub hlt.le]; ring
          rw [e5]; exact hth
      rw [hek]; ring
  beta_reduce
  rw [hfib, Finset.card_image_of_injOn, Finset.card_range]
  intro k hk k' hk' hkk
  simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
  have h' : c - (k : ZMod n) = c - (k' : ZMod n) := hkk
  have h'' : (k : ZMod n) = (k' : ZMod n) := by linear_combination -h'
  have h3 := congrArg ZMod.val h''
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at h3

theorem lenT_le_three (c : ZMod n) (hc : ¬ th (c + 1))
    (halt : ∀ i, ¬ (th i ∧ th (i + 1) ∧ th (i + 2))) : lenT th c ≤ 3 := by
  obtain ⟨-, -, -, hlt⟩ := lenT_spec th c hc
  by_contra hcon
  push_neg at hcon
  have a1 := hlt 1 le_rfl (by omega)
  have a2 := hlt 2 (by norm_num) (by omega)
  have a3 := hlt 3 (by norm_num) (by omega)
  apply halt (c - 2)
  have e3 : c - 2 = c - ((3:ℕ) : ZMod n) + 1 := by push_cast; ring
  have e2 : c - 2 + 1 = c - ((2:ℕ) : ZMod n) + 1 := by push_cast; ring
  have e1 : c - 2 + 2 = c - ((1:ℕ) : ZMod n) + 1 := by push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e3]; exact a3
  · rw [e2]; exact a2
  · rw [e1]; exact a1

theorem lenT_le_R (c : ZMod n) (hc : ¬ th (c + 1)) (R : ℕ)
    (hone : ∀ i, ¬ ∀ u : ℕ, u < R → th (i + (u : ZMod n))) : lenT th c ≤ R := by
  obtain ⟨-, -, -, hlt⟩ := lenT_spec th c hc
  by_contra hcon
  push_neg at hcon
  apply hone (c - (R : ZMod n) + 1)
  intro u hu
  have hth := hlt (R - u) (by omega) (by omega)
  have e : c - (R : ZMod n) + 1 + (u : ZMod n) = c - ((R - u : ℕ) : ZMod n) + 1 := by
    rw [Nat.cast_sub hu.le]; ring
  rw [e]; exact hth

end Comb

section ThetaShiftProofs

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem hmax_le [NeZero n] (Mi hi : ZMod n → ℕ) (j : ZMod n) :
    Mi j + hi j ≤ Formalism.MainNotions.LiftingTheory.Hmax n Mi hi := by
  unfold Formalism.MainNotions.LiftingTheory.Hmax
  have hj : ((j.val : ℕ) : ZMod n) = j := ZMod.natCast_zmod_val j
  calc Mi j + hi j = (fun k : ℕ => Mi (k : ZMod n) + hi (k : ZMod n)) j.val := by
        simp only [hj]
    _ ≤ _ := Finset.le_sup (f := fun k : ℕ => Mi (k : ZMod n) + hi (k : ZMod n))
        (Finset.mem_range.mpr (ZMod.val_lt j))

theorem killsΔ_mono (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {r r' : ℕ} (hr : r ≤ r') (h : Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W r)) :
    Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W r') := by
  intro y hy hδ
  have hk := h y hy hδ
  have e : Formalism.MainNotions.LiftingTheory.lp W r' = ((PD.p : ℕ) : LetA O n) ^ (r' - r) * Formalism.MainNotions.LiftingTheory.lp W r := by
    unfold Formalism.MainNotions.LiftingTheory.lp
    rw [← pow_add, Nat.sub_add_cancel hr]
  rw [e, mul_smul]
  exact Submodule.smul_mem _ _ hk

def rrB (l h w S η : ℕ) : ℝ :=
  2 * ((w : ℝ) + S + η) / l + 2 * (h : ℝ) / (l : ℝ) ^ 2 + 2 * Real.logb l (2 * (h : ℝ)) + 3

theorem kill_cut [NeZero n] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (CR : ℝ)
    (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR) {T T' : LocLat G Qp LL O} (Φ : LatHom T.L T'.L)
    (hS : Formalism.MainNotions.LiftingTheory.Sur W Φ) (Mi hi : ZMod n → ℕ) (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi hi)
    (hl : 11 ≤ PD.p) (h w S η : ℕ) (hη : η + 1 ≤ h) (hH : ∀ i, Mi i + hi i ≤ h + η) (c : ZMod n)
    (hc : Mi (c + 1) + hi (c + 1) ≤ w + S + η) :
    Formalism.MainNotions.LiftingTheory.KillsΔ W Φ c (Formalism.MainNotions.LiftingTheory.lp W ⌊rrB PD.p h w S η⌋₊) := by
  obtain ⟨hs, -, hr, hk, -⟩ := hWR hcase T T' Φ Mi hi hS hJ c
  have hl' : (11:ℝ) ≤ (PD.p:ℝ) := by exact_mod_cast hl
  have hHm : Formalism.MainNotions.LiftingTheory.Hmax n Mi hi ≤ h + η := by
    unfold Formalism.MainNotions.LiftingTheory.Hmax
    exact Finset.sup_le (fun k _ => hH _)
  have hcc : ((Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) : ℕ) : ℝ) =
      ((cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) : ℕ) : ℝ) := rfl
  have hfa : ∀ a : ℕ, (((Mi (c + ((a + 1 : ℕ) : ZMod n)) + hi (c + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ) +
      (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) : ℝ) + 3) ≤
      (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi : ℝ) + (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) : ℝ) + 3 := by
    intro a
    have h' : ((Mi (c + ((a + 1 : ℕ) : ZMod n)) + hi (c + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ) ≤
        (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi : ℝ) := by exact_mod_cast hmax_le Mi hi _
    linarith
  have h0 : (((Mi (c + ((0 + 1 : ℕ) : ZMod n)) + hi (c + ((0 + 1 : ℕ) : ZMod n)) : ℕ) : ℝ) +
      (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) : ℝ) + 3) ≤
      ((Mi (c + 1) + hi (c + 1) : ℕ) : ℝ) + (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) : ℝ) + 3 := by
    have e0 : c + ((0 + 1 : ℕ) : ZMod n) = c + 1 := by push_cast; ring
    rw [e0]
  have hsum := tsum_three PD.p hl
    (fun a : ℕ => (((Mi (c + ((a + 1 : ℕ) : ZMod n)) + hi (c + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ) +
      (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) : ℝ) + 3))
    (((Mi (c + 1) + hi (c + 1) : ℕ) : ℝ) + (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) : ℝ) + 3)
    ((Formalism.MainNotions.LiftingTheory.Hmax n Mi hi : ℝ) + (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) : ℝ) + 3)
    ((Formalism.MainNotions.LiftingTheory.Hmax n Mi hi : ℝ) + (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) : ℝ) + 3)
    (fun a => by positivity) h0 (hfa 1) (fun a _ => hfa a)
  beta_reduce at hsum
  have hs2 := le_trans hs hsum
  have hdiv : ((Formalism.MainNotions.LiftingTheory.Hmax n Mi hi : ℝ) + (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) : ℝ) + 3) /
        ((PD.p : ℝ) - 1) +
      ((Formalism.MainNotions.LiftingTheory.Hmax n Mi hi : ℝ) + (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) : ℝ) + 3) /
        (((PD.p : ℝ) - 1) * ((PD.p : ℝ) - 2)) =
      ((Formalism.MainNotions.LiftingTheory.Hmax n Mi hi : ℝ) + (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) : ℝ) + 3) /
        ((PD.p : ℝ) - 2) := by
    have h1' : (PD.p : ℝ) - 1 ≠ 0 := by linarith
    have h2' : (PD.p : ℝ) - 2 ≠ 0 := by linarith
    field_simp <;> ring
  have hr' := hr
  rw [hcc] at hr'
  obtain ⟨key, -⟩ := rr_le PD.p hl h w S η (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) (Mi (c + 1) + hi (c + 1))
    hη hHm hc _ _ (by rw [← hcc]; linarith) hr'
  apply killsΔ_mono W Φ c _ hk
  apply Nat.le_floor
  unfold rrB
  exact key

theorem arcBasic_core [NeZero n] [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ}
    {up : ZMod n → Bool} {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi) :
    let A := arcOf b w S η up size
    A.OK ∧ (∑ c ∈ A.cuts, A.len c) = n ∧
    (Alt b η up size → ∀ c ∈ A.cuts, A.len c ≤ 3) ∧
    (∀ R : ℕ, 1 ≤ R → One b η R up size → ∀ c ∈ A.cuts, A.len c ≤ R) ∧
    (A.σ PD.p : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := by
  intro A
  obtain ⟨hl, ⟨-, -, hηs, -, -, hthin, -⟩, h20w, -, -, hex⟩ := hB
  have hth : ∀ c ∈ A.cuts, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c + 1) :=
    fun c hc => (Finset.mem_filter.mp hc).2
  have hlen : ∀ c, A.len c = lenT (Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size) c := fun c => rfl
  have hmemc : ∀ c, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c + 1) → c ∈ A.cuts :=
    fun c hc => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  have hw1 : 1 ≤ w := by
    obtain ⟨i, hi⟩ := hex
    have h1 := hthin i hi
    have h2 := hηs i
    omega
  have hG : w + S ≤ Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size := by
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
    split_ifs <;> omega
  have h1 : 1 ≤ Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size := le_trans (by omega) hG
  have hsz : ∀ i, (A.ty i).size = size i := by
    intro i
    show Formalism.MainNotions.LocalTheoryWindows.LT.size
      (if up i then Formalism.MainNotions.LocalTheoryWindows.LT.up (size i) else Formalism.MainNotions.LocalTheoryWindows.LT.down (size i)) = size i
    split <;> rfl
  have hOK : A.OK := by
    unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.OK
    refine ⟨?_, le_rfl, ?_, ?_, ?_, hG, h1, ?_, ?_⟩
    · obtain ⟨i, hi⟩ := hex
      exact ⟨i - 1, hmemc _ (by rw [sub_add_cancel]; exact hi)⟩
    · intro c hc
      obtain ⟨hl1, hln, hlf, hlt⟩ := lenT_spec _ c (hth c hc)
      rw [hlen]
      exact ⟨hl1, hln, hmemc _ hlf, fun d hd1 hd2 hmem => hth _ hmem (hlt d hd1 hd2)⟩
    · intro c hc
      rw [hlen]
      exact (lenT_spec _ c (hth c hc)).1
    · intro i
      show Formalism.MainNotions.LocalTheoryWindows.LT.ok η
        (if up i then Formalism.MainNotions.LocalTheoryWindows.LT.up (size i) else Formalism.MainNotions.LocalTheoryWindows.LT.down (size i))
      split <;> exact hηs i
    · intro i _
      rw [hsz]
      show size i + S ≤ Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size
      by_cases hT : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i
      · have hex' : ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i := ⟨i, hT⟩
        unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
        rw [if_pos hex']
        have := hT.2
        omega
      · have := hthin i hT
        unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
        split_ifs <;> omega
    · right
      refine ⟨rfl, ?_, ?_⟩
      · intro i
        show Formalism.MainNotions.LocalTheoryWindows.LT.thick
          (if up i then Formalism.MainNotions.LocalTheoryWindows.LT.up (size i) else Formalism.MainNotions.LocalTheoryWindows.LT.down (size i)) = true
        split <;> rfl
      · intro c hc
        rw [hsz]
        show size (c + 1) + S ≤ w + S
        have := hthin (c + 1) (hth c hc)
        omega
  refine ⟨hOK, ?_, ?_, ?_, ?_⟩
  · exact sum_lenT (Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size) hex
  · intro hAlt c hc
    rw [hlen]
    exact lenT_le_three _ c (hth c hc) (fun i => (hAlt i).2)
  · intro R _ hOne c hc
    rw [hlen]
    exact lenT_le_R _ c (hth c hc) R hOne.2
  · have hsg := sig_le PD.p hl (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size) w S η h1 hG
    have hσ : A.σ PD.p = ⌈(((2 * (w + S) : ℕ) : ℝ) +
        ((2 * Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size / (PD.p - 1) + 1 : ℕ) : ℝ)) * PD.p /
          ((PD.p : ℝ) - 1) ^ 2 + 1⌉₊ := by
      show ⌈(((2 * (w + S) : ℕ) : ℝ) +
        ((2 * Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size / (PD.p - 1) + 1 : ℕ) : ℝ) / (PD.p : ℝ) ^ (1 - 1)) *
          PD.p / ((PD.p : ℝ) - 1) ^ 2 + 1⌉₊ = _
      rw [Nat.sub_self, pow_zero, div_one]
    rw [hσ]
    exact hsg

theorem arcSetup_of [NeZero n] [Fintype (K →ₐ[Qp] LL)] [FiniteDimensional Qp LL]
    (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR) (hJmp : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O)
    (hT₂ : ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a) :
    let A := arcOf b w S η up size
    A.OK ∧ Win W A T₁ ∧ Win W A T₂ ∧ (∑ c ∈ A.cuts, A.len c) = n ∧
    (Alt b η up size → ∀ c ∈ A.cuts, A.len c ≤ 3) ∧
    (∀ R : ℕ, 1 ≤ R → One b η R up size → ∀ c ∈ A.cuts, A.len c ≤ R) ∧
    (A.σ PD.p : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ∧
    ∃ rr : ℕ, (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ∧
      (∀ c ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr)) ∧
      ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L) (cc : G → T₂.V),
        cc ∈ latticeCocycles T₂.L → IsCrys PD Y.ρ → Formalism.MainNotions.LiftingTheory.IsExtOf W ι π cc →
          Win W A Y ∧ ∀ c ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W π c (Formalism.MainNotions.LiftingTheory.lp W rr) := by
  intro A
  have hB' := hB
  obtain ⟨hl, ⟨-, hSur, hηs, hJ1, -, hthin, -⟩, h20w, -, -, hex⟩ := hB
  obtain ⟨hOK, hsum, hAlt, hOne, hσ⟩ := arcBasic_core W F hB'
  obtain ⟨hcrone, hjone⟩ := Formalism.MainNotions.LiftingTheory.lone_HOne0 W
  have hwin : ∀ i, (A.ty i).win A.G₀ A.S A.η =
      (if up i then Set.Icc (size i : ℤ) ((size i : ℤ) + S) ∪ Set.Icc (-(η : ℤ)) η
        else Set.Icc (-(size i : ℤ) - S) (-(size i : ℤ)) ∪ Set.Icc (-(η : ℤ)) η) := by
    intro i
    show Formalism.MainNotions.LocalTheoryWindows.LT.win (w + S) S η
      (if up i then Formalism.MainNotions.LocalTheoryWindows.LT.up (size i) else Formalism.MainNotions.LocalTheoryWindows.LT.down (size i)) = _
    split <;> rfl
  have h0win : ∀ i, (0:ℤ) ∈ (A.ty i).win A.G₀ A.S A.η := by
    intro i
    rw [hwin i]
    split
    · exact Set.mem_union_right _ (Set.mem_Icc.mpr ⟨by omega, by omega⟩)
    · exact Set.mem_union_right _ (Set.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hG : w + S ≤ Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size := by
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
    split_ifs <;> omega
  have hsizeB : ∀ i, size i + S ≤ Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size := by
    intro i
    by_cases hT : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i
    · have hex' : ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i := ⟨i, hT⟩
      unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
      rw [if_pos hex']
      have := hT.2
      omega
    · have := hthin i hT
      unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
      split_ifs <;> omega
  have hηB : η + 1 ≤ Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size := by
    obtain ⟨i, hi⟩ := hex
    have h1 := hthin i hi
    have h2 := hηs i
    omega
  obtain ⟨Mi', hMi'⟩ : ∃ f : ZMod n → ℕ, ∀ i, f i = if up i then η else size i + S :=
    ⟨_, fun i => rfl⟩
  obtain ⟨hi', hhi'⟩ : ∃ f : ZMod n → ℕ, ∀ i, f i = if up i then size i + S else η :=
    ⟨_, fun i => rfl⟩
  have hMH : ∀ i, Mi' i + hi' i = size i + S + η := by
    intro i; rw [hMi' i, hhi' i]; split_ifs <;> omega
  have hHb : ∀ i, Mi' i + hi' i ≤ Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size + η := by
    intro i; rw [hMH i]; have := hsizeB i; omega
  have hcb : ∀ c ∈ A.cuts, Mi' (c + 1) + hi' (c + 1) ≤ w + S + η := by
    intro c hc
    rw [hMH (c + 1)]
    have := hthin (c + 1) (Finset.mem_filter.mp hc).2
    omega
  have hJL : ∀ T : LocLat G Qp LL O, Win W A T → Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi' hi' := by
    intro T hT i τ hτ a ha
    have hm := hT.2 i τ hτ a ha
    rw [hwin i] at hm
    have hsi := hηs i
    rw [Set.mem_Icc, hMi' i, hhi' i]
    by_cases hu : up i = true
    · rw [if_pos hu] at hm
      rw [if_pos hu, if_pos hu]
      rcases hm with hm | hm <;> rw [Set.mem_Icc] at hm <;> constructor <;> omega
    · rw [if_neg hu] at hm
      rw [if_neg hu, if_neg hu]
      rcases hm with hm | hm <;> rw [Set.mem_Icc] at hm <;> constructor <;> omega
  have hW1 : Win W A T₁ := by
    unfold Formalism.MainNotions.ArcLiftingSetup.Win
    refine ⟨hSur.1, fun i => ?_⟩
    rw [hwin i]
    exact hJ1 i
  have hW2 : Win W A T₂ := by
    unfold Formalism.MainNotions.ArcLiftingSetup.Win
    refine ⟨hSur.2.1, fun i τ hτ a ha => ?_⟩
    exact hW1.2 i τ hτ a (hT₂ τ a ha)
  have hrrB : rrB PD.p (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size) w S η ≤
      3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size :=
    (rr_le PD.p hl (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size) w S η 0 0 hηB (Nat.zero_le _) (Nat.zero_le _)
      _ _ le_rfl le_rfl).2
  have hrrB0 : 0 ≤ rrB PD.p (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size) w S η := by
    unfold rrB
    have hp11 : (11:ℝ) ≤ PD.p := by exact_mod_cast hl
    have hp : (1:ℝ) < PD.p := by linarith
    have hB1 : (1:ℝ) ≤ (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ) := by
      exact_mod_cast (show 1 ≤ Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size by omega)
    have hL := Real.logb_nonneg hp (show (1:ℝ) ≤ 2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ) by linarith)
    have q1 : 0 ≤ 2 * ((w:ℝ) + S + η) / PD.p := by positivity
    have q2 : 0 ≤ 2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ) / (PD.p : ℝ) ^ 2 := by positivity
    linarith
  refine ⟨hOK, hW1, hW2, hsum, hAlt, hOne, hσ, ⌊rrB PD.p (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size) w S η⌋₊,
    le_trans (Nat.floor_le hrrB0) hrrB, ?_, ?_⟩
  · intro c hc
    exact kill_cut W hcase CR hWR F hSur Mi' hi' (hJL T₁ hW1) hl _ w S η hηB hHb c (hcb c hc)
  · intro Y ι π cc _ hY hext
    obtain ⟨hses, -⟩ := hext
    have hses' := hses
    obtain ⟨-, -, honto, -, -⟩ := hses'
    have hWY : Win W A Y := by
      unfold Formalism.MainNotions.ArcLiftingSetup.Win
      refine ⟨hY, fun i τ hτ a ha => ?_⟩
      rcases (hJmp T₂ Y W.one ι π hses hSur.2.1 hY hcrone τ a).mp ha with h2 | h1
      · exact hW2.2 i τ hτ a h2
      · rw [hjone τ a h1]
        exact h0win i
    refine ⟨hWY, fun c hc => ?_⟩
    have hSπ : Formalism.MainNotions.LiftingTheory.Sur W π := by
      unfold Formalism.MainNotions.LiftingTheory.Sur
      exact ⟨hY, hcrone, honto⟩
    exact kill_cut W hcase CR hWR π hSπ Mi' hi' (hJL Y hWY) hl _ w S η hηB hHb c (hcb c hc)

end ThetaShiftProofs

end Formalism.MainNotions.N.FrobeniusPowerSeries.SetupA
