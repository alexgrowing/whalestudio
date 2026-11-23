import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FamilyFourthBound
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentStatementHolds
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ThresholdLowerBounds

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem coarse_bounds {r : ℕ} (g P : ℕ) (f : Fin (r + 1) → ℕ) (hf : ∀ c, f c < P) (hs : ∑ c, f c ≤ g)
    (hd : P ∣ g - ∑ c, f c) :
    (((g - ∑ c, f c) / P : ℕ) : ℝ) * P ≤ g ∧
      (g : ℝ) - ((r : ℝ) + 1) * P < (((g - ∑ c, f c) / P : ℕ) : ℝ) * P := by
  have h1 : (g - ∑ c, f c) / P * P = g - ∑ c, f c := Nat.div_mul_cancel hd
  have h2 : ∑ c, f c < (r + 1) * P := by
    calc ∑ c, f c < ∑ _c : Fin (r + 1), P :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun c _ => hf c)
      _ = (r + 1) * P := by simp
  have h3 : (((g - ∑ c, f c) / P : ℕ) : ℝ) * P = (g : ℝ) - ((∑ c, f c : ℕ) : ℝ) := by
    rw [← Nat.cast_sub hs, ← Nat.cast_mul, h1]
  have h4 : ((∑ c, f c : ℕ) : ℝ) < ((r : ℝ) + 1) * P := by exact_mod_cast h2
  have h5 : (0 : ℝ) ≤ ((∑ c, f c : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [h3]
  constructor <;> linarith

theorem poly_S {de ε be : ℝ} (hε : 0 ≤ ε) (hde : 40 * ε ≤ de) (hde6 : de < 1 / 6) (hbe : be ≤ de / 2 - 18 * ε) :
    (1 - 2 * de) * (1 + be) * (1 + de) ≤ 1 - ε := by
  have hde0 : 0 ≤ de := by linarith
  have hu : 0 ≤ (1 - 2 * de) * (1 + de) := mul_nonneg (by linarith) (by linarith)
  have h1 : (1 + be) * ((1 - 2 * de) * (1 + de)) ≤ (1 + de / 2 - 18 * ε) * ((1 - 2 * de) * (1 + de)) :=
    mul_le_mul_of_nonneg_right (by linarith) hu
  have h2 : (1 + de / 2 - 18 * ε) * ((1 - 2 * de) * (1 + de)) ≤ (1 + de / 2) * ((1 - 2 * de) * (1 + de)) :=
    mul_le_mul_of_nonneg_right (by linarith) hu
  have h3 : (1 + de / 2) * ((1 - 2 * de) * (1 + de)) = 1 - de / 2 - 5 / 2 * de ^ 2 - de ^ 3 := by ring
  have h4 : 0 ≤ de ^ 2 := by positivity
  have h5 : 0 ≤ de ^ 3 := by positivity
  calc (1 - 2 * de) * (1 + be) * (1 + de) = (1 + be) * ((1 - 2 * de) * (1 + de)) := by ring
    _ ≤ 1 - de / 2 - 5 / 2 * de ^ 2 - de ^ 3 := by linarith
    _ ≤ 1 - ε := by linarith

theorem poly_U {de ε be : ℝ} (hε : 0 ≤ ε) (hde : 40 * ε ≤ de) (hde6 : de < 1 / 6) (hbe : be ≤ de / 2 - 18 * ε) :
    1 ≤ (1 - be - ε) * ((1 - de) * (1 + 2 * de)) := by
  have hde0 : 0 ≤ de := by linarith
  have hu : 0 ≤ (1 - de) * (1 + 2 * de) := mul_nonneg (by linarith) (by linarith)
  have h1 : (1 - de / 2) * ((1 - de) * (1 + 2 * de)) ≤ (1 - be - ε) * ((1 - de) * (1 + 2 * de)) :=
    mul_le_mul_of_nonneg_right (by linarith) hu
  have h3 : (1 - de / 2) * ((1 - de) * (1 + 2 * de)) = 1 + de * (1 / 2 - 5 / 2 * de + de ^ 2) := by ring
  have h4 : 0 ≤ de * (1 / 2 - 5 / 2 * de + de ^ 2) := mul_nonneg hde0 (by nlinarith [sq_nonneg de])
  linarith

theorem dich_S {a b' de ε be E0 Q Qj P pd g A A0 : ℝ} (ha : 0 < a) (hb : 0 < b') (hP : 0 < P) (hpd : 0 < pd)
    (hQj : P * pd = Qj) (hQ : Qj ≤ Q) (hε : 0 ≤ ε) (hde : 40 * ε ≤ de) (hde6 : de < 1 / 6)
    (hbe : be ≤ de / 2 - 18 * ε) (hbe0 : 0 ≤ be) (hN5 : E0 / a + Q / a ≤ ε) (hg : g ≤ b' * (1 + be))
    (hA : A * P ≤ g) (hA0 : (a - E0) / Qj - 1 < A0) (hS : pd < a / b' * (1 - 2 * de)) :
    A * (1 + de) < A0 := by
  have hde0 : 0 ≤ de := by linarith
  have hQj0 : 0 < Qj := by rw [← hQj]; positivity
  have h1 : pd * b' < a * (1 - 2 * de) := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hb] at hS; exact hS
  have h2 : A * Qj ≤ b' * (1 + be) * pd := by
    rw [← hQj, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_trans hA hg) hpd.le
  have h3 : b' * (1 + be) * pd ≤ a * (1 - 2 * de) * (1 + be) := by
    have := mul_le_mul_of_nonneg_right h1.le (by linarith : (0 : ℝ) ≤ 1 + be)
    linarith
  have h4 := poly_S hε hde hde6 hbe
  have h5 : a * (1 - ε) < A0 * Qj := by
    have e1 : E0 + Q ≤ ε * a := by
      rw [← add_div, div_le_iff₀ ha] at hN5; exact hN5
    have e2 : (a - E0) / Qj - 1 = (a - E0 - Qj) / Qj := by field_simp
    rw [e2, div_lt_iff₀ hQj0] at hA0
    linarith
  have h6 : A * (1 + de) * Qj ≤ a * (1 - ε) := by
    have e1 : A * Qj * (1 + de) ≤ a * (1 - 2 * de) * (1 + be) * (1 + de) :=
      mul_le_mul_of_nonneg_right (le_trans h2 h3) (by linarith)
    have e2 : a * ((1 - 2 * de) * (1 + be) * (1 + de)) ≤ a * (1 - ε) := mul_le_mul_of_nonneg_left h4 ha.le
    linarith
  exact lt_of_mul_lt_mul_right (lt_of_le_of_lt h6 h5) hQj0.le

theorem dich_U {a b' de ε be E0 Qj P pd g A A0 k : ℝ} (hb : 0 < b') (hP : 0 < P) (hpd : 0 < pd)
    (hQj : P * pd = Qj) (hε : 0 ≤ ε) (hde : 40 * ε ≤ de) (hde6 : de < 1 / 6)
    (hbe : be ≤ de / 2 - 18 * ε) (hE0 : 0 ≤ E0) (hg : b' * (1 - be) ≤ g) (hkP : k * P ≤ ε * b')
    (hA : g - k * P < A * P) (hA0 : A0 ≤ (a - E0) / Qj) (hU : a / b' * (1 + 2 * de) < pd) :
    A0 < A * (1 - de) := by
  have hde0 : 0 ≤ de := by linarith
  have hQj0 : 0 < Qj := by rw [← hQj]; positivity
  have h1 : a * (1 + 2 * de) < pd * b' := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hb] at hU; exact hU
  have h2 : A0 * Qj ≤ a := by
    rw [le_div_iff₀ hQj0] at hA0; linarith
  have h3 : b' * (1 - be - ε) < A * P := by nlinarith
  have h4 : b' * (1 - be - ε) * pd < A * Qj := by
    rw [← hQj, ← mul_assoc]
    exact mul_lt_mul_of_pos_right h3 hpd
  have h5 := poly_U hε hde hde6 hbe
  have hv : 0 < (1 - de) * (1 + 2 * de) := mul_pos (by linarith) (by linarith)
  have h6 : pd * b' ≤ b' * (1 - be - ε) * pd * ((1 - de) * (1 + 2 * de)) := by
    have := mul_le_mul_of_nonneg_left h5 (mul_pos hpd hb).le
    linarith
  have h7 : b' * (1 - be - ε) * pd * ((1 - de) * (1 + 2 * de)) < A * Qj * ((1 - de) * (1 + 2 * de)) :=
    mul_lt_mul_of_pos_right h4 hv
  have h8 : A0 * Qj * (1 + 2 * de) ≤ a * (1 + 2 * de) := mul_le_mul_of_nonneg_right h2 (by linarith)
  have h9 : A0 * (Qj * (1 + 2 * de)) < A * (1 - de) * (Qj * (1 + 2 * de)) := by linarith
  exact lt_of_mul_lt_mul_right h9 (mul_pos hQj0 (by linarith)).le

section Plug

variable {C0 Cde CE1 CE2 H : ℝ} {X : Loc}

theorem Std.p1 (h : Std C0 Cde CE1 CE2 H X) : (1 : ℝ) ≤ X.p := by
  have := h.p5
  exact_mod_cast (by omega : 1 ≤ X.p)

def eps (X : Loc) (C0 : ℝ) : ℝ := X.N1 * X.La C0 / X.k

theorem Std.eps_ge (h : Std C0 Cde CE1 CE2 H X) : 1 / X.k ≤ eps X C0 := by
  have hk : 0 < X.k := by linarith [h.k5]
  have h2 : (1 : ℝ) ≤ X.N1 := by exact_mod_cast h.N1pos
  unfold eps
  exact div_le_div_of_nonneg_right (one_le_mul_of_one_le_of_one_le h2 h.La1) hk.le

theorem Std.eps0 (h : Std C0 Cde CE1 CE2 H X) : 0 ≤ eps X C0 := by
  have hk : 0 < X.k := by linarith [h.k5]
  exact le_trans (by positivity) h.eps_ge

theorem Std.kQ (hH : 1 ≤ H) (h : Std C0 Cde CE1 CE2 H X) : X.k ^ 3 * X.Q ≤ X.b' := by
  have hk : 0 < X.k := by linarith [h.k5]
  have hQ1 := h.Q1
  have hQ0 : 0 < X.Q := by linarith
  have hQ4 : X.Q ≤ X.Q ^ 4 := by
    calc X.Q = X.Q ^ 1 := (pow_one _).symm
      _ ≤ X.Q ^ 4 := pow_le_pow_right₀ hQ1 (by norm_num)
  have hHNY : 1 ≤ H * X.N * X.Y :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hH (by linarith [h.N2])) h.Y1
  have a1 : X.k ^ 3 * X.Q ≤ X.k ^ 3 * X.Q ^ 4 := mul_le_mul_of_nonneg_left hQ4 (by positivity)
  have a2 : X.k ^ 3 * X.Q ^ 4 * 1 ≤ X.k ^ 3 * X.Q ^ 4 * (H * X.N * X.Y) :=
    mul_le_mul_of_nonneg_left hHNY (by positivity)
  have a3 := h.Hb
  nlinarith

theorem Std.kQeps (hH : 1 ≤ H) (h : Std C0 Cde CE1 CE2 H X) : X.k * X.Q ≤ eps X C0 * X.b' := by
  have hk5 := h.k5
  have hk : 0 < X.k := by linarith
  have hQ0 : 0 < X.Q := by linarith [h.Q1]
  have h1 := h.kQ hH
  have h2 : 1 / X.k * X.b' ≤ eps X C0 * X.b' := mul_le_mul_of_nonneg_right h.eps_ge h.bpos.le
  have h3 : X.k * X.Q ≤ 1 / X.k * X.b' := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hk]
    have : X.k * X.Q * X.k ≤ X.k ^ 3 * X.Q := by
      have : X.k * X.Q * X.k * 1 ≤ X.k * X.Q * X.k * X.k :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    linarith
  linarith

theorem Std.two_rank_mul_Q_le (hH : 1 ≤ H) (h : Std C0 Cde CE1 CE2 H X) : 2 * (X.k * X.Q) ≤ X.b' := by
  have hk5 := h.k5
  have hk : 0 < X.k := by linarith
  have hQ0 : 0 < X.Q := by linarith [h.Q1]
  have h1 := h.kQ hH
  have : X.k * X.Q * 2 ≤ X.k * X.Q * (X.k * X.k) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  nlinarith

theorem Std.levels (h : Std C0 Cde CE1 CE2 H X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    (0 : ℝ) < ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) ∧
    (0 : ℝ) < (X.p : ℝ) ^ ((segDists X.TT j).get i) ∧
    ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) * (X.p : ℝ) ^ ((segDists X.TT j).get i) =
      ((X.p ^ segG X.TT j : ℕ) : ℝ) ∧
    ((X.p ^ segG X.TT j : ℕ) : ℝ) ≤ X.Q ∧
    ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) ≤ ((X.p ^ segG X.TT j : ℕ) : ℝ) := by
  obtain ⟨_, hdG⟩ := dist_pos_lt X.TT j i
  have hp1 := h.p1
  have hp0 : (0 : ℝ) < X.p := by linarith
  refine ⟨by push_cast; positivity, by positivity, ?_, ?_, ?_⟩
  · push_cast
    rw [← pow_add]
    congr 1
    omega
  · push_cast
    exact pow_le_pow_right₀ hp1 (h.segB j).1
  · push_cast
    exact pow_le_pow_right₀ hp1 (Nat.sub_le _ _)

theorem coarse_degree_alternative (hH : 1 ≤ H) (h : Std C0 Cde CE1 CE2 H X) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (i : Fin (segS X.TT j)) :
    ((i : ℕ) < (X.seg C0 CE1 CE2 j).sigma →
      (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * (1 + X.de C0 Cde) < ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ)) ∧
    ((X.seg C0 CE1 CE2 j).sigma ≤ (i : ℕ) →
      ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) < (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * (1 - X.de C0 Cde)) := by
  have hodd := dist_odd h.nEven X.TT j i
  have hmem := (pos_mem X.TT j i).1
  obtain ⟨hb1, hb2⟩ := h.winB _ hmem
  obtain ⟨hP0, hpd0, hQj, hQ, hPQ⟩ := h.levels j i
  have hcb := coarse_bounds (X.bT (segPos X.TT j i)) (X.p ^ (segG X.TT j - (segDists X.TT j).get i)) (b.rz i)
    (fun c => (hd.1 i c).1) (hd.2.1 i).1 (hd.2.1 i).2
  have hsig := sigma_iff X.p (by have := h.p5; omega) X.TT X.bT X.a X.b' X.Y (X.La C0) (X.E0 C0 CE1 CE2) j i
  have hband := h.band _ hodd
  have hde : 40 * eps X C0 ≤ X.de C0 Cde := by
    have := h.LaK
    unfold eps
    calc 40 * (X.N1 * X.La C0 / X.k) = 40 * X.N1 * X.La C0 / X.k := by ring
      _ ≤ _ := this
  have hbe : be X C0 ≤ X.de C0 Cde / 2 - 18 * eps X C0 := by
    have := h.beLe
    unfold eps
    calc be X C0 ≤ X.de C0 Cde / 2 - 18 * X.N1 * X.La C0 / X.k := this
      _ = _ := by ring
  have hde0 : 0 ≤ X.de C0 Cde := by linarith [h.eps0]
  have hab0 : 0 < (X.a : ℝ) / X.b' := div_pos h.apos h.bpos
  have hk0 : 0 < X.k := by linarith [h.k5]
  constructor
  · intro hi
    have hlt : (X.p : ℝ) ^ ((segDists X.TT j).get i) < (X.a : ℝ) / X.b' := hsig.1 hi
    have hS : (X.p : ℝ) ^ ((segDists X.TT j).get i) < (X.a : ℝ) / X.b' * (1 - 2 * X.de C0 Cde) := by
      by_contra hcon
      exact hband ⟨not_lt.1 hcon, by nlinarith⟩
    exact dich_S (Q := X.Q) (E0 := X.E0 C0 CE1 CE2) h.apos h.bpos hP0 hpd0 hQj hQ h.eps0 hde h.de6 hbe h.be0 h.N5 hb2
      hcb.1 (Int.sub_one_lt_floor _) hS
  · intro hi
    have hge : (X.a : ℝ) / X.b' ≤ (X.p : ℝ) ^ ((segDists X.TT j).get i) :=
      not_lt.1 (fun hc => absurd (hsig.2 hc) (not_lt.2 hi))
    have hU : (X.a : ℝ) / X.b' * (1 + 2 * X.de C0 Cde) < (X.p : ℝ) ^ ((segDists X.TT j).get i) := by
      by_contra hcon
      exact hband ⟨by nlinarith, not_lt.1 hcon⟩
    have hkP : X.k * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) ≤ eps X C0 * X.b' :=
      le_trans (mul_le_mul_of_nonneg_left (le_trans hPQ hQ) hk0.le) (h.kQeps hH)
    exact dich_U (k := X.k) (E0 := X.E0 C0 CE1 CE2) h.bpos hP0 hpd0 hQj h.eps0 hde h.de6 hbe h.E0nn hb1 hkP
      hcb.2 (Int.floor_le _) hU

theorem sg_le_of_std (hH : 1 ≤ H) (h : Std C0 Cde CE1 CE2 H X) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (aTop : Fin (segS X.TT j) → ℕ) (ha : ∀ i, (X.a : ℝ) ≤ aTop i)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) aTop b) (i : Fin (segS X.TT j))
    (hsg : (b.sg i : ℝ) ≤ 2 * (X.seg C0 CE1 CE2 j).La * ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) / ((X.m : ℝ) + 1)) :
    b.sg i ≤ coarseC X.p (X.seg C0 CE1 CE2 j) aTop b i := by
  obtain ⟨hP0, hpd0, hQj, hQ, hPQ⟩ := h.levels j i
  have hcb := coarse_bounds (aTop i) (X.p ^ (segG X.TT j - (segDists X.TT j).get i)) (b.ry i)
    (fun c => (hd.1 i c).2) (hd.2.2 i).1 (hd.2.2 i).2
  have hk0 : 0 < X.k := by linarith [h.k5]
  have hQj0 : (0 : ℝ) < ((X.p ^ segG X.TT j : ℕ) : ℝ) := lt_of_lt_of_le hP0 hPQ
  have hA0 : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) ≤ ((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j : ℕ) : ℝ) :=
    Int.floor_le _
  have hA0' : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * ((X.p ^ segG X.TT j : ℕ) : ℝ) ≤ X.a := by
    rw [le_div_iff₀ hQj0] at hA0
    linarith [h.E0nn]
  have hLa0 : 0 ≤ X.La C0 := by linarith [h.La1]
  have h4 : 4 * X.La C0 ≤ X.k := by nlinarith [h.LaN, h.N2]
  have hsg' : (b.sg i : ℝ) * X.k ≤ 2 * X.La C0 * ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) := by
    rw [le_div_iff₀ (by exact hk0)] at hsg
    exact hsg
  have hsg0 : (0 : ℝ) ≤ (b.sg i : ℝ) := Nat.cast_nonneg _

  have h5 : (b.sg i : ℝ) * ((X.p ^ segG X.TT j : ℕ) : ℝ) * X.k ≤ X.k * X.a / 2 := by
    have e1 : (b.sg i : ℝ) * X.k * ((X.p ^ segG X.TT j : ℕ) : ℝ) ≤
        2 * X.La C0 * ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * ((X.p ^ segG X.TT j : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hsg' hQj0.le
    have e2 : 2 * X.La C0 * (((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * ((X.p ^ segG X.TT j : ℕ) : ℝ)) ≤
        2 * X.La C0 * X.a := mul_le_mul_of_nonneg_left hA0' (by linarith)
    have e3 : 4 * X.La C0 * X.a ≤ X.k * X.a := mul_le_mul_of_nonneg_right h4 h.apos.le
    linarith
  have h6 : (b.sg i : ℝ) * ((X.p ^ segG X.TT j : ℕ) : ℝ) ≤ X.a / 2 := by
    have : (b.sg i : ℝ) * ((X.p ^ segG X.TT j : ℕ) : ℝ) * X.k ≤ X.a / 2 * X.k := by linarith
    exact le_of_mul_le_mul_right this hk0
  have h7 : (b.sg i : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) ≤ X.a / 2 :=
    le_trans (mul_le_mul_of_nonneg_left hPQ hsg0) h6
  have h8 : X.k * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) ≤ X.a / 2 := by
    have e1 := mul_le_mul_of_nonneg_left (le_trans hPQ hQ) hk0.le
    have e2 := h.two_rank_mul_Q_le hH
    have e3 := h.ba
    linarith
  have h9 : (b.sg i : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) <
      (coarseC X.p (X.seg C0 CE1 CE2 j) aTop b i : ℝ) *
        ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) := by
    have e1 : (aTop i : ℝ) - X.k * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) <
      (coarseC X.p (X.seg C0 CE1 CE2 j) aTop b i : ℝ) *
        ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) := hcb.2
    have e2 := ha i
    linarith
  have h10 : (b.sg i : ℝ) < (coarseC X.p (X.seg C0 CE1 CE2 j) aTop b i : ℝ) := lt_of_mul_lt_mul_right h9 hP0.le
  exact le_of_lt (by exact_mod_cast h10)

theorem kept_transfer (hH : 1 ≤ H) (h : Std C0 Cde CE1 CE2 H X) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (aTop aTop' : Fin (segS X.TT j) → ℕ) (ha : ∀ i, (X.a : ℝ) ≤ aTop' i)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) aTop' b) (hK : Kept X.p X.m (X.seg C0 CE1 CE2 j) aTop b) :
    Kept X.p X.m (X.seg C0 CE1 CE2 j) aTop' b := by
  obtain ⟨_, hU, hS, hO⟩ := hK
  refine ⟨hd, hU, fun i hi => ?_, hO⟩
  obtain ⟨s1, s2, _, s4, s5⟩ := hS i hi
  exact ⟨s1, s2, sg_le_of_std hH h j b aTop' ha hd i s5, s4, s5⟩

end Plug

theorem remainderSegmentBoundFirst (D : Formalism.BasicNotions.D7) : RemainderSegmentBoundFirst D := by
  unfold RemainderSegmentBoundFirst
  refine TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1) ?_
  intro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 X _ hD hI hc j b
    hd i
  exact coarse_degree_alternative le_rfl (std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc) j b hd i

theorem restFree (D : Formalism.BasicNotions.D7) : RestFree D := by
  unfold RestFree
  refine TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1) ?_
  intro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 X aT' hD hI hI' hc
    j b hd hd'
  have h := std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc
  constructor
  · exact kept_transfer le_rfl h j b _ _ (fun i => (hI'.2.1 _ (pos_mem X.TT j i).1).1) hd'
  · exact kept_transfer le_rfl h j b _ _ (fun i => (hI.2.1 _ (pos_mem X.TT j i).1).1) hd

end Formalism.MainNotions.ColumnSystems.Pf
