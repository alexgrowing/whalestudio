import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PageOKRun
import Development.AbelianVarietyTheory.Proofs.HeightProofs.XLeOfSqLeFMulR

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.RunJoin.InhAll
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Num GlobalTheory.RunJoin GlobalTheory.RunJoin.Inh
open GlobalTheory.Survey.NumericBoundConstants

def prog (p l g : ℕ) (i : Fin p) : ℕ := l + (p - 1 - i.1) * g

theorem prog_anti (p l g : ℕ) : Antitone (prog p l g) := by
  intro i k hik
  have h : i.1 ≤ k.1 := hik
  show l + (p - 1 - k.1) * g ≤ l + (p - 1 - i.1) * g
  have : p - 1 - k.1 ≤ p - 1 - i.1 := by omega
  exact Nat.add_le_add_left (Nat.mul_le_mul_right g this) l

theorem gapZ_prog (p l g : ℕ) (i : Fin p) : gapZ (prog p l g) i = if i.1 + 1 < p then (g : ℤ) else l := by
  unfold gapZ
  by_cases h : i.1 + 1 < p
  · rw [dif_pos h, if_pos h]
    show ((l + (p - 1 - i.1) * g : ℕ) : ℤ) - ((l + (p - 1 - (i.1 + 1)) * g : ℕ) : ℤ) = g
    have e : p - 1 - i.1 = (p - 1 - (i.1 + 1)) + 1 := by omega
    rw [e]
    push_cast
    ring
  · rw [dif_neg h, if_neg h]
    show ((l + (p - 1 - i.1) * g : ℕ) : ℤ) = l
    have e : p - 1 - i.1 = 0 := by omega
    rw [e]
    simp

theorem prog_last (p l g : ℕ) (i : Fin p) (h : ¬ i.1 + 1 < p) : prog p l g i = l := by
  have : i.1 = p - 1 := by omega
  simp [prog, this]

def twoW (D : D7) (j l l' g n : ℕ) (hn : Even n) : WeightFamilies.Wt D j where
  aP _ := prog _ l g
  aM _ := prog _ l' g
  aPlus_antitone _ := prog_anti _ _ _
  aM_anti _ := prog_anti _ _ _
  n := n
  n_even := hn

variable {D : D7} {j : ℕ}

def mu (D : D7) (j : ℕ) : ℝ := ((max (D.R.sigW j).2 1 : ℕ) : ℝ)

theorem one_le_mu : 1 ≤ mu D j := by
  unfold mu
  have : 1 ≤ max (D.R.sigW j).2 1 := le_max_right _ _
  exact_mod_cast this

theorem mu_le_r : mu D j ≤ D.R.r := by
  unfold mu
  have hr := Formalism.BasicNotions.Ranks.r_eq D.R
  have hk := Formalism.BasicNotions.Ranks.k_ge D.R
  have : max (D.R.sigW j).2 1 ≤ D.R.r := by
    show max (D.R.m - j) 1 ≤ D.R.r
    apply max_le <;> omega
  exact_mod_cast this

theorem DF_twoW (l l' g n : ℕ) (hn : Even n) :
    (DF (twoW D j l l' g n hn) : ℝ) = D.R.f * (sA (D.R.sigW j).1 l g + sA (D.R.sigW j).2 l' g) := by
  have hcard : (Fintype.card D.what₂.Tau : ℝ) = D.R.f := by
    have e := Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.sum_apW (D := D) D.R.m 1 0 (2 * 0) (even_two_mul 0)
    simp only [Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.apW_aM, Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.apW_aP] at e
    simp only [mul_zero, add_zero, Nat.cast_zero, Nat.cast_one, Finset.sum_const_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.sA] at e
    rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.sigW_m_fst] at e
    have hr : (0 : ℝ) < D.R.r := by exact_mod_cast Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.r_pos D
    exact mul_right_cancel₀ (ne_of_gt hr) e
  have e : DF (twoW D j l l' g n hn) = Fintype.card D.what₂.Tau *
      ((∑ i : Fin (D.R.sigW j).1, prog _ l g i) + ∑ i : Fin (D.R.sigW j).2, prog _ l' g i) := by
    simp only [DF, degP, twoW, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [e, Nat.cast_mul, hcard, Nat.cast_add, Nat.cast_sum, Nat.cast_sum]
  rfl

theorem size_eq (w : WeightFamilies.Wt D j) : w.size = DF w + D.R.f * mu D j * D.R.r * w.n + 1 := by
  simp only [WeightFamilies.Wt.size, DF, degP, mu]
  push_cast
  ring

theorem sig_add (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := by
  have hr := Formalism.BasicNotions.Ranks.r_eq D.R
  have hk := Formalism.BasicNotions.Ranks.k_ge D.R
  show (D.R.k + j - 1) + (D.R.m - j) = D.R.r
  omega

theorem dimY_eq_top (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : WeightFamilies.dimY D j = Dm D := by
  show WeightFamilies.dimY D j = WeightFamilies.dimY D D.R.m
  rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.dimY_m D]
  unfold WeightFamilies.dimY
  rw [GlobalTheory.ConstCompare.choose_two_add, sig_add h1 h2]

theorem DF_twoW_le (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {l l' g n : ℕ} (hn : Even n) (hl : l' ≤ l) :
    (DF (twoW D j l l' g n hn) : ℝ) ≤ (D.R.f : ℝ) * D.R.r * ((l : ℝ) + D.R.r * g) := by
  rw [DF_twoW]
  have hpq : ((D.R.sigW j).1 : ℝ) + (D.R.sigW j).2 = D.R.r := by exact_mod_cast sig_add h1 h2
  have a1 := sA_le (D.R.sigW j).1 l g
  have a2 := sA_le (D.R.sigW j).2 l' g
  have hl' : (l' : ℝ) ≤ l := by exact_mod_cast hl
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ (D.R.sigW j).1 := Nat.cast_nonneg _
  have hq : (0 : ℝ) ≤ (D.R.sigW j).2 := Nat.cast_nonneg _
  have hg : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  rw [← hpq, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hf
  nlinarith [mul_le_mul_of_nonneg_left hl' hq, mul_nonneg (mul_nonneg hp hq) hg]

theorem n0_le_Ns (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : n0 D j ≤ D.R.r + 2 * g0 D * (Dm D + 1) := by
  have key : D.R.f * (D.R.sigW j).1 * (D.R.sigW j).2 ≤ D.R.f * ((D.R.sigW j).1 * (D.R.sigW j).2 +
      (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) / 2 + (D.R.sigW j).2 * ((D.R.sigW j).2 - 1) / 2) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  unfold n0
  rw [← dimY_eq_top h1 h2]
  unfold WeightFamilies.dimY
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right key 1)) _

section Run
variable (X : RunN D) (j)

def ka : WeightFamilies.Wt D j := twoW D j X.kl (X.Tq * X.Q0) (X.Tq * X.Q - 2) D.R.nV X.nV_even

def wL : WeightFamilies.Wt D j := twoW D j X.Q0 X.Q0 X.Q X.nW X.nW_even

def wF : WeightFamilies.Wt D j :=
  twoW D j ((Dm D + 2) * X.nW + 2 * D.R.r + (Dm D + 2) * X.Q0) ((Dm D + 2) * X.Q0) ((Dm D + 2) * X.Q - 2) X.nP X.even_nP₂

variable {j}

theorem Tp_eq (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : Tp D j X.T = X.Tq := by
  first
  | (rw [RunN.Tq_eq, Tp, dimY_eq_top h1 h2])
  | (simp only [RunN.Tq, Tp, dimY_eq_top h1 h2])

private lemma int_fdiv_mul_self_left (a b : ℤ) (ha : 0 < a) : Int.fdiv (a * b) a = b := by
  first
  | exact Int.mul_fdiv_cancel_left b (ne_of_gt ha)
  | (rw [Int.fdiv_eq_ediv_of_nonneg _ ha.le]; exact Int.mul_ediv_cancel_left b (ne_of_gt ha))
  | (rw [Int.fdiv_eq_ediv_of_dvd (dvd_mul_right a b)]; exact Int.mul_ediv_cancel_left b (ne_of_gt ha))
  | simp [Int.fdiv_eq_ediv_of_nonneg, ha.le, ne_of_gt ha]

theorem isL (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : IsL D (ka j X) (wL j X) X.T X.nW := by
  have hT : Tp D j X.T = X.Tq := Tp_eq X h1 h2
  have hD : WeightFamilies.dimY D j = Dm D := dimY_eq_top h1 h2
  have hpos : (0 : ℤ) < (X.Tq : ℤ) := by have := X.two_le_Tq; omega
  have hTQ : (((X.Tq * X.Q - 2 : ℕ)) : ℤ) + 2 = (X.Tq : ℤ) * X.Q := by
    rw [Nat.cast_sub X.two_le_TqQ]; push_cast; ring
  have hkl : ((X.kl : ℕ) : ℤ) - ((Dm D : ℤ) + 2) * X.nW - 2 * D.R.r = (X.Tq : ℤ) * X.Q0 := by
    simp only [RunN.kl]; push_cast; ring
  refine ⟨rfl, ?_, ?_⟩
  · intro τ i
    dsimp only [ka, wL, twoW]
    rw [gapZ_prog, gapZ_prog, hT]
    split_ifs with h
    · rw [hTQ, int_fdiv_mul_self_left _ _ hpos]
    · rw [prog_last _ _ _ _ h, hD, hkl, int_fdiv_mul_self_left _ _ hpos]
  · intro τ i
    dsimp only [ka, wL, twoW]
    rw [gapZ_prog, gapZ_prog, hT]
    split_ifs with h
    · rw [hTQ, int_fdiv_mul_self_left _ _ hpos]
    · rw [prog_last _ _ _ _ h]
      push_cast
      rw [int_fdiv_mul_self_left _ _ hpos]

theorem isF : IsF' (ka j X) (wL j X) (wF j X) X.T X.nP := by
  have e3 : (X.Tq : ℤ) = X.T + Dm D + 2 := by rw [X.Tq_eq]; push_cast; ring
  refine ⟨rfl, ?_, ?_⟩
  · intro τ i
    dsimp only [ka, wL, wF, twoW, prog]
    simp only [RunN.kl]
    push_cast [Nat.cast_sub X.two_le_TqQ, Nat.cast_sub X.two_le_DQ]
    rw [e3]
    simp only [RunN.Q]
    push_cast
    ring
  · intro τ i
    dsimp only [ka, wL, wF, twoW, prog]
    push_cast [Nat.cast_sub X.two_le_TqQ, Nat.cast_sub X.two_le_DQ]
    rw [e3]
    simp only [RunN.Q]
    push_cast
    ring

theorem gap_prog (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {p l : ℕ} (i : Fin p) (h : i.1 + 1 < p) :
    ((Tp D j X.T * (Tp D j X.T + 2 * D.R.r) : ℕ) : ℤ) ≤ gapZ (prog p l (X.Tq * X.Q - 2)) i + 2 := by
  rw [gapZ_prog, if_pos h, Tp_eq X h1 h2, Nat.cast_sub X.two_le_TqQ]
  simp only [RunN.Q]
  push_cast
  apply le_of_eq
  ring

theorem ncAt_ka (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) : (X.kl : ℤ) + D.R.t + 1 ≤ ncAt (ka j X) τ := by
  have hp : 0 < (D.R.sigW j).1 := by
    have hk := Formalism.BasicNotions.Ranks.k_ge (R := D.R)
    show 0 < D.R.k + j - 1
    omega
  have hpq : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := sig_add h1 h2
  have hn : (ka j X).n = D.R.r + D.R.t := rfl
  have e : (ka j X).aP τ ⟨(D.R.sigW j).1 - 1, by omega⟩ = X.kl :=
    prog_last _ _ _ _ (by show ¬ ((D.R.sigW j).1 - 1 + 1 < (D.R.sigW j).1); omega)
  unfold ncAt
  rw [dif_pos hp]
  split_ifs <;> omega

theorem DF_ka_le (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    (DF (ka j X) : ℝ) ≤ (D.R.f : ℝ) * D.R.r * ((X.kl : ℝ) + D.R.r * ((X.Tq : ℝ) * X.Q)) := by
  have hl : X.Tq * X.Q0 ≤ X.kl := Nat.le_add_left (X.Tq * X.Q0) ((Dm D + 2) * X.nW + 2 * D.R.r)
  refine (DF_twoW_le (g := X.Tq * X.Q - 2) (n := D.R.nV) h1 h2 X.nV_even hl).trans ?_
  have hg : ((X.Tq * X.Q - 2 : ℕ) : ℝ) ≤ (X.Tq : ℝ) * X.Q := by
    have : X.Tq * X.Q - 2 ≤ X.Tq * X.Q := Nat.sub_le _ _
    exact_mod_cast this
  have hfr : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by positivity
  have hr : (0 : ℝ) ≤ D.R.r := by positivity
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hg hr)) hfr

theorem DF_wL_le (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    (DF (wL j X) : ℝ) ≤ (D.R.f : ℝ) * D.R.r * ((X.Q0 : ℝ) + D.R.r * X.Q) := DF_twoW_le (n := X.nW) h1 h2 X.nW_even le_rfl

theorem T_wL_le : (X.T : ℝ) * (wL j X).size ≤ (ka j X).size + X.T := by
  have hDk : (DF (ka j X) : ℝ) = D.R.f * (sA (D.R.sigW j).1 X.kl (X.Tq * X.Q - 2) +
      sA (D.R.sigW j).2 (X.Tq * X.Q0) (X.Tq * X.Q - 2)) :=
    DF_twoW (D := D) (j := j) X.kl (X.Tq * X.Q0) (X.Tq * X.Q - 2) D.R.nV X.nV_even
  have hDL : (DF (wL j X) : ℝ) = D.R.f * (sA (D.R.sigW j).1 X.Q0 X.Q + sA (D.R.sigW j).2 X.Q0 X.Q) :=
    DF_twoW (D := D) (j := j) X.Q0 X.Q0 X.Q X.nW X.nW_even
  have hsK : (ka j X).size = DF (ka j X) + D.R.f * mu D j * D.R.r * D.R.nV + 1 := size_eq _
  have hsL : (wL j X).size = DF (wL j X) + D.R.f * mu D j * D.R.r * X.nW + 1 := size_eq _
  have hT : X.T ≤ X.Tq := by rw [X.Tq_eq]; omega
  have hTQ0 : X.T * X.Q0 ≤ X.Tq * X.Q0 := Nat.mul_le_mul_right _ hT
  have hkl : X.Tq * X.Q0 ≤ X.kl := Nat.le_add_left (X.Tq * X.Q0) ((Dm D + 2) * X.nW + 2 * D.R.r)
  have hsplitQ : X.Tq * X.Q = X.T * X.Q + (Dm D + 2) * X.Q := by rw [X.Tq_eq]; ring
  have hgk : X.T * X.Q ≤ X.Tq * X.Q - 2 :=
    Nat.le_sub_of_add_le (by rw [hsplitQ]; exact Nat.add_le_add_left X.two_le_DQ _)
  have i1 := sA_lin (p := (D.R.sigW j).1) (l1 := X.Q0) (g1 := X.Q) (l2 := X.kl) (g2 := X.Tq * X.Q - 2)
    (a1 := (X.T : ℝ)) (a2 := 1) (e := 0) (fun c _ => by
      rw [one_mul, add_zero]
      have : X.T * (X.Q0 + c * X.Q) ≤ X.kl + c * (X.Tq * X.Q - 2) := by
        calc X.T * (X.Q0 + c * X.Q) = X.T * X.Q0 + c * (X.T * X.Q) := by ring
          _ ≤ X.kl + c * (X.Tq * X.Q - 2) := Nat.add_le_add (hTQ0.trans hkl) (Nat.mul_le_mul_left c hgk)
      exact_mod_cast this)
  have i2 := sA_lin (p := (D.R.sigW j).2) (l1 := X.Q0) (g1 := X.Q) (l2 := X.Tq * X.Q0) (g2 := X.Tq * X.Q - 2)
    (a1 := (X.T : ℝ)) (a2 := 1) (e := 0) (fun c _ => by
      rw [one_mul, add_zero]
      have : X.T * (X.Q0 + c * X.Q) ≤ X.Tq * X.Q0 + c * (X.Tq * X.Q - 2) := by
        calc X.T * (X.Q0 + c * X.Q) = X.T * X.Q0 + c * (X.T * X.Q) := by ring
          _ ≤ X.Tq * X.Q0 + c * (X.Tq * X.Q - 2) := Nat.add_le_add hTQ0 (Nat.mul_le_mul_left c hgk)
      exact_mod_cast this)
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  have j1 := mul_le_mul_of_nonneg_left i1 hf0
  have j2 := mul_le_mul_of_nonneg_left i2 hf0
  have hmu := one_le_mu (D := D) (j := j)
  have hfmr : (0 : ℝ) ≤ D.R.f * mu D j * D.R.r :=
    mul_nonneg (mul_nonneg hf0 (by linarith)) (by positivity)
  have hsplit : (D.R.nV : ℝ) = X.nP + X.T * X.nW := by exact_mod_cast X.split
  have hnP := mul_nonneg hfmr (Nat.cast_nonneg (α := ℝ) X.nP)
  rw [hsK, hsL, hDk, hDL, hsplit]
  linarith

theorem wF_size_le (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : (wF j X).size ≤ ((Dm D : ℝ) + 2) * (wL j X).size +
    2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 + (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * X.nP + 1 := by
  have hDF : (DF (wF j X) : ℝ) = D.R.f * (sA (D.R.sigW j).1 ((Dm D + 2) * X.nW + 2 * D.R.r + (Dm D + 2) * X.Q0)
      ((Dm D + 2) * X.Q - 2) + sA (D.R.sigW j).2 ((Dm D + 2) * X.Q0) ((Dm D + 2) * X.Q - 2)) :=
    DF_twoW (D := D) (j := j) ((Dm D + 2) * X.nW + 2 * D.R.r + (Dm D + 2) * X.Q0) ((Dm D + 2) * X.Q0)
      ((Dm D + 2) * X.Q - 2) X.nP X.even_nP₂
  have hDL : (DF (wL j X) : ℝ) = D.R.f * (sA (D.R.sigW j).1 X.Q0 X.Q + sA (D.R.sigW j).2 X.Q0 X.Q) :=
    DF_twoW (D := D) (j := j) X.Q0 X.Q0 X.Q X.nW X.nW_even
  have hsF : (wF j X).size = DF (wF j X) + D.R.f * mu D j * D.R.r * X.nP + 1 := size_eq _
  have hsL : (wL j X).size = DF (wL j X) + D.R.f * mu D j * D.R.r * X.nW + 1 := size_eq _
  have hDQ : ((((Dm D + 2) * X.Q - 2 : ℕ)) : ℝ) = ((Dm D : ℝ) + 2) * X.Q - 2 := by
    rw [Nat.cast_sub X.two_le_DQ]; push_cast; ring
  have i1 := sA_lin (p := (D.R.sigW j).1) (l1 := (Dm D + 2) * X.nW + 2 * D.R.r + (Dm D + 2) * X.Q0)
    (g1 := (Dm D + 2) * X.Q - 2) (l2 := X.Q0) (g2 := X.Q)
    (a1 := 1) (a2 := ((Dm D : ℝ) + 2)) (e := ((Dm D : ℝ) + 2) * X.nW + 2 * D.R.r) (fun c _ => by
      rw [one_mul]
      have : (Dm D + 2) * X.nW + 2 * D.R.r + (Dm D + 2) * X.Q0 + c * ((Dm D + 2) * X.Q - 2) ≤
          (Dm D + 2) * (X.Q0 + c * X.Q) + ((Dm D + 2) * X.nW + 2 * D.R.r) := by
        calc (Dm D + 2) * X.nW + 2 * D.R.r + (Dm D + 2) * X.Q0 + c * ((Dm D + 2) * X.Q - 2)
            ≤ (Dm D + 2) * X.nW + 2 * D.R.r + (Dm D + 2) * X.Q0 + c * ((Dm D + 2) * X.Q) :=
              Nat.add_le_add_left (Nat.mul_le_mul_left c (Nat.sub_le _ _)) _
          _ = (Dm D + 2) * (X.Q0 + c * X.Q) + ((Dm D + 2) * X.nW + 2 * D.R.r) := by ring
      exact_mod_cast this)
  have i2 := sA_lin (p := (D.R.sigW j).2) (l1 := (Dm D + 2) * X.Q0)
    (g1 := (Dm D + 2) * X.Q - 2) (l2 := X.Q0) (g2 := X.Q)
    (a1 := 1) (a2 := ((Dm D : ℝ) + 2)) (e := 0) (fun c _ => by
      rw [one_mul, add_zero]
      have : (Dm D + 2) * X.Q0 + c * ((Dm D + 2) * X.Q - 2) ≤ (Dm D + 2) * (X.Q0 + c * X.Q) := by
        calc (Dm D + 2) * X.Q0 + c * ((Dm D + 2) * X.Q - 2)
            ≤ (Dm D + 2) * X.Q0 + c * ((Dm D + 2) * X.Q) :=
              Nat.add_le_add_left (Nat.mul_le_mul_left c (Nat.sub_le _ _)) _
          _ = (Dm D + 2) * (X.Q0 + c * X.Q) := by ring
      exact_mod_cast this)
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  have hr0 : (0 : ℝ) ≤ D.R.r := by positivity
  have hD0 : (0 : ℝ) ≤ Dm D := by positivity
  have hW0 : (0 : ℝ) ≤ X.nW := by positivity
  have hP0 : (0 : ℝ) ≤ X.nP := by positivity
  have j1 := mul_le_mul_of_nonneg_left i1 hf0
  have j2 := mul_le_mul_of_nonneg_left i2 hf0
  have hmu := one_le_mu (D := D) (j := j)
  have hpr : (((D.R.sigW j).1 : ℕ) : ℝ) ≤ D.R.r := by
    have := sig_add (D := D) h1 h2
    exact_mod_cast (show (D.R.sigW j).1 ≤ D.R.r by omega)
  have hnPW : (X.nP : ℝ) ≤ X.nW := by exact_mod_cast X.nP_le_nW
  have a1 : 0 ≤ (D.R.f : ℝ) * (((Dm D : ℝ) + 2) * X.nW) * (D.R.r - (D.R.sigW j).1) :=
    mul_nonneg (mul_nonneg hf0 (by positivity)) (by linarith)
  have a2 : 0 ≤ (D.R.f : ℝ) * D.R.r * (D.R.r - (D.R.sigW j).1) :=
    mul_nonneg (mul_nonneg hf0 hr0) (by linarith)
  have a3 : 0 ≤ (D.R.f : ℝ) * D.R.r * (mu D j - 1) * (((Dm D : ℝ) + 2) * X.nW - X.nP) :=
    mul_nonneg (mul_nonneg (mul_nonneg hf0 hr0) (by linarith)) (by nlinarith)
  have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast r_pos D
  have a4 : 0 ≤ (D.R.f : ℝ) * X.nP * (D.R.r * (D.R.r - 1)) :=
    mul_nonneg (mul_nonneg hf0 hP0) (mul_nonneg hr0 (by linarith))
  rw [hsF, hsL, hDF, hDL]
  linarith

end Run

theorem domAt_index {L : SizeData₂ D} {nW : ℕ} {CP : ℝ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (h : DomAt D L D.R.m nW CP) :
    DomAt D L j nW CP := by
  unfold DomAt at h ⊢
  obtain ⟨hC, hC20, hlam, hPN, hlog, hPU, hPO, _, hP12, hP73⟩ := h
  refine ⟨hC, hC20, hlam, hPN, hlog, hPU, hPO, ?_, hP12, ?_⟩
  ·
    have hn := n0_le_Ns (D := D) h1 h2
    have hd : Dm D = D.R.f * D.R.r.choose 2 := dimY_m D
    have hc : D.R.r.choose 2 ≤ D.R.r ^ 2 := by
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self _ _).trans (by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have hN : n0 D j ≤ D.R.r + 2 * (2 * 5 ^ 4 * D.R.r) * (D.R.f * D.R.r ^ 2 + 1) := by
      calc n0 D j ≤ D.R.r + 2 * g0 D * (Dm D + 1) := hn
        _ ≤ D.R.r + 2 * (2 * 5 ^ 4 * D.R.r) * (D.R.f * D.R.r ^ 2 + 1) := by
          rw [hd]; unfold g0; gcongr
    have hN' : (n0 D j : ℝ) ≤ (D.R.r : ℝ) + 2 * (2 * 5 ^ 4 * (D.R.r : ℝ)) * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 + 1) := by
      exact_mod_cast hN
    have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f_ge D
    have hr : (6 : ℝ) ≤ D.R.r := by exact_mod_cast r_ge D
    have hL : (1 : ℝ) ≤ L.sc.L := one_le_L L
    have hR3 : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 3 := by positivity
    have hFR2 : (1 : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by nlinarith
    have a1 : (D.R.r : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 3 := by
      have := mul_le_mul_of_nonneg_left hFR2 (by linarith : (0 : ℝ) ≤ D.R.r)
      nlinarith
    have a2 : 64 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 3) ≤ ((D.R.f : ℝ) * D.R.r) ^ 3 := by
      have h64 : (64 : ℝ) ≤ (D.R.f : ℝ) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_right h64 hR3
      nlinarith
    have hFR : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by positivity
    have h3 : ((D.R.f : ℝ) * D.R.r) ^ 3 ≤ ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 3 := by
      apply pow_le_pow_left₀ hFR
      nlinarith
    have h4 : (D.R.r : ℝ) + 2 * (2 * 5 ^ 4 * (D.R.r : ℝ)) * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 + 1) ≤
        1000 * ((D.R.f : ℝ) * D.R.r) ^ 3 := by nlinarith
    have hZb : Zb D L = (D.R.f : ℝ) * D.R.r * L.sc.L := rfl
    rw [hZb]
    calc (n0 D j : ℝ) ≤ _ := hN'
      _ ≤ 1000 * ((D.R.f : ℝ) * D.R.r) ^ 3 := h4
      _ ≤ CP * ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 3 := mul_le_mul hC h3 (by positivity) (by linarith)
  · have e : DivisibilityWeightConstant D j = DivisibilityWeightConstant D D.R.m := by unfold DivisibilityWeightConstant; rw [dimY_eq_top h1 h2]
    rw [e]; exact hP73

theorem extra_le {A k b s PP TO rd r D2 nW nP q0 : ℝ} (h : Rn A k b s PP TO rd r D2 nW nP q0) {μ : ℝ} (hμ : μ ≤ r) :
    μ * A * (nP + TO * nW) ≤ A * b := by
  have hA := h.forty_eight_le_constant
  have hT := h.one_le_order_alt
  have hnW := h.nW_le
  have hn40 := h.forty_le_weight_count
  have hnP0 := h.projectivePointSizes
  have hnPW := h.nPW
  have hrA := h.rA
  have hr6 := h.r6
  have hb := h.sq_mul_sq_le
  have hTT := h.TO_le_sq
  have hX0 : 0 ≤ nP + TO * nW := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ TO) (by linarith : (0 : ℝ) ≤ nW)
    linarith
  have h1 : TO * nW ≤ TO ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hnW (by linarith)
  have hX : nP + TO * nW ≤ 2 * TO ^ 2 := by linarith
  have h3 : r * (nP + TO * nW) ≤ r * (2 * TO ^ 2) := mul_le_mul_of_nonneg_left hX (by linarith)
  have h5 : 2 * r ≤ A ^ 2 := by nlinarith
  have h4 : r * (2 * TO ^ 2) ≤ A ^ 2 * TO ^ 2 := by
    calc r * (2 * TO ^ 2) = (2 * r) * TO ^ 2 := by ring
      _ ≤ A ^ 2 * TO ^ 2 := mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
  have hrX : r * (nP + TO * nW) ≤ b := by linarith
  calc μ * A * (nP + TO * nW) ≤ r * A * (nP + TO * nW) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ (by linarith)) hX0
    _ = A * (r * (nP + TO * nW)) := by ring
    _ ≤ A * b := mul_le_mul_of_nonneg_left hrX (by linarith)

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

section Record
variable (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
include h1 h2

theorem DF_ka_add_le : (DF (ka j (runOf T S hZ)) : ℝ) + 1 ≤ 4 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
  have R := rn_of T S hZ
  have hD := DF_ka_le (runOf T S hZ) h1 h2
  rw [ekl T S hZ, eTq T S hZ, eQ T S hZ] at hD
  have hX : 0 ≤ (D.R.f : ℝ) * D.R.r * ((T.nP : ℝ) + T.TO * T.nWn) := by positivity
  apply R.sK
  nlinarith [hD, hX]

theorem ka_size_le : (ka j (runOf T S hZ)).size ≤ 5 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
  have R := rn_of T S hZ
  have hs := size_eq (ka j (runOf T S hZ))
  have hsp : D.R.nV = T.nP + T.TO * T.nWn := (runOf T S hZ).split
  have hn : (ka j (runOf T S hZ)).n = T.nP + T.TO * T.nWn := hsp
  have hD := DF_ka_add_le T S hZ h1 h2
  have hE := extra_le R (mu_le_r (D := D) (j := j))
  rw [hs, hn]
  push_cast
  nlinarith [hD, hE]

theorem wL_size_le : (wL j (runOf T S hZ)).size * (T.TO : ℝ) ≤ 3 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
  have R := rn_of T S hZ
  have hs := size_eq (wL j (runOf T S hZ))
  have hn : (wL j (runOf T S hZ)).n = T.nWn := rfl
  have hD0 := DF_wL_le (runOf T S hZ) h1 h2
  rw [eQ T S hZ] at hD0
  have hD : (DF (wL j (runOf T S hZ)) : ℝ) ≤ (D.R.f : ℝ) * D.R.r *
      ((q0N T : ℝ) + D.R.r * ((T.TO : ℝ) + ((T.Dp : ℝ) + 2) + 2 * D.R.r)) := hD0
  have hAn : 0 ≤ (D.R.f : ℝ) * D.R.r * (T.nWn : ℝ) := by positivity
  have hL := R.sL (s := (D.R.f : ℝ) * D.R.r *
      ((q0N T : ℝ) + D.R.r * ((T.TO : ℝ) + ((T.Dp : ℝ) + 2) + 2 * D.R.r)) + 1) (by linarith)
  have hE := extra_le R (mu_le_r (D := D) (j := j))
  have hmu := one_le_mu (D := D) (j := j)
  have hTO : (0 : ℝ) ≤ T.TO := by positivity
  have hD' := mul_le_mul_of_nonneg_right hD hTO
  have hP : 0 ≤ mu D j * ((D.R.f : ℝ) * D.R.r) * (T.nP : ℝ) :=
    mul_nonneg (mul_nonneg (by linarith) (by positivity)) (by positivity)
  rw [hs, hn]
  nlinarith [hD', hL, hE, hP]

theorem setC_of {B : WeightFamilies.Prov D} {Q : ModuliIntegralCharts.Prov D} (X : PJ D B Q j) (hO : OPO L B) {C A : ℝ} (hD : DomAt D L j T.nWn C) :
    SetC L X 10 C A (ka j (runOf T S hZ)) (wL j (runOf T S hZ)) (wF j (runOf T S hZ)) T.TO T.nP T.nWn (h0R T) := by
  have hTpos : 0 < T.TO := by have := T.TO_40; omega
  have hd : WeightFamilies.dimY D j = T.Dp := (dimY_eq_top h1 h2).trans (dm_eq T)
  have hb0 : (0 : ℝ) ≤ L.sc.b := (Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.b_pos L).le
  have hkf : (0 : ℝ) ≤ (D.R.k : ℝ) * D.R.f * L.sc.b :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hb0
  have hAk := mul_le_mul_of_nonneg_right (A_le_kf (D := D)) hb0
  have h2T : 2 * (T.TO : ℝ) ^ 2 ≤ ((runOf T S hZ).kl : ℝ) := two_mul_order_sq_le_length T S hZ
  unfold SetC
  refine ⟨rfl, fun τ i hi => ?_, fun τ i hi => ?_, ?_, fun τ => ?_, fun τ i hi => ?_, fun τ i hi => ?_, ?_,
    T.even_nP₂, T.nP_ge, T.nW_lo.2.2, ?_, T.nW_lo.1, (runOf T S hZ).split, isL (runOf T S hZ) h1 h2,
    isF (runOf T S hZ), ?_, ?_, ?_, ?_, ?_, T.nW_40, ?_, ?_, hO, hD⟩
  · exact gap_prog (runOf T S hZ) h1 h2 (l := (runOf T S hZ).kl) i hi
  · exact gap_prog (runOf T S hZ) h1 h2 (l := (runOf T S hZ).Tq * (runOf T S hZ).Q0) i hi
  · unfold h0R; exact le_rfl
  · have h := ncAt_ka (runOf T S hZ) h1 h2 τ
    have h' : ((runOf T S hZ).kl : ℝ) + D.R.t + 1 ≤ (ncAt (ka j (runOf T S hZ)) τ : ℝ) := by exact_mod_cast h
    have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    unfold h0R
    nlinarith [sq_nonneg (T.TO : ℝ)]
  · have e : (ka j (runOf T S hZ)).aP τ i = (runOf T S hZ).kl := prog_last _ _ _ i (by omega)
    rw [e]; unfold h0R; linarith
  · have e : (ka j (runOf T S hZ)).aM τ i = (runOf T S hZ).Tq * (runOf T S hZ).Q0 :=
      prog_last _ _ _ i (by omega)
    rw [e]
    have hR := rn_of T S hZ
    have hq : L.sc.b ≤ (T.TO : ℝ) * (q0N T : ℝ) := hR.q0lo
    have hA : ((D.R.f : ℝ) * D.R.r) ^ 2 * (T.TO : ℝ) ^ 2 ≤ L.sc.b := hR.sq_mul_sq_le
    have h48 : (48 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := hR.forty_eight_le_constant
    have hTq : T.TO ≤ (runOf T S hZ).Tq := by
      show T.TO ≤ T.TO + WeightFamilies.dimY D D.R.m + 2; omega
    have hTq' : (T.TO : ℝ) ≤ ((runOf T S hZ).Tq : ℝ) := by exact_mod_cast hTq
    have hq0 : (0 : ℝ) ≤ (q0N T : ℝ) := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_right hTq' hq0
    have hsq : 2 * (T.TO : ℝ) ^ 2 ≤ ((D.R.f : ℝ) * D.R.r) ^ 2 * (T.TO : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); nlinarith
    have ec : (((runOf T S hZ).Tq * (runOf T S hZ).Q0 : ℕ) : ℝ) = ((runOf T S hZ).Tq : ℝ) * (q0N T : ℝ) := by
      push_cast; rfl
    rw [ec]; unfold h0R; linarith
  · have h := ka_size_le T S hZ h1 h2
    nlinarith
  · unfold sizeConstantAtParamsWeight; exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · have hT : (0 : ℝ) < (T.TO : ℝ) := by exact_mod_cast hTpos
    rw [le_div_iff₀ hT]
    have h := wL_size_le T S hZ h1 h2
    nlinarith
  · exact hTpos
  · rw [hd]; have := T.TO_40; omega
  · rw [hd]; exact T.TO_40
  · rw [hd]; exact T.TO_nW
  · calc n0 D j ≤ _ := n0_le_Ns h1 h2
      _ = D.R.r + 2 * (2 * 5 ^ 4 * D.R.r) * (T.Dp + 1) := by rw [← dm_eq T]; try rfl
      _ ≤ T.TO := T.order_ge_rank_bound
  · rw [hd]; exact T.TO_11D2

end Record

end GlobalTheory.RunJoin.InhAll
