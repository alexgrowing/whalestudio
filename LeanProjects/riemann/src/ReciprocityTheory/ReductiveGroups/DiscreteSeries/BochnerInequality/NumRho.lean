import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section NumRho

variable {ε : Fin n → Bool}

theorem numRho_dot_root_left (a b : Fin n) (v : Fin n → ℝ) : dot (root a b) v = v a - v b := by
  simp [dot, root, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]

theorem numRho_dot_root_right (a b : Fin n) (v : Fin n → ℝ) : dot v (root a b) = v a - v b := by
  simp [dot, root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem numRho_cardR (p : Fin n → Prop) [DecidablePred p] :
    ((univ.filter p).card : ℝ) = ∑ c, if p c then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole]

private theorem rhoC_bound (ε : Fin n → Bool) (a : Fin n) :
    |2 * rhoC ε a| + 1 ≤ ((univ.filter fun c => ε c = ε a).card : ℝ) := by
  have h2 : 2 * rhoC ε a = ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) -
      ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) := by
    simp only [rhoC]
    ring
  have hU : (0:ℝ) ≤ ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) := Nat.cast_nonneg _
  have hL : (0:ℝ) ≤ ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) := Nat.cast_nonneg _
  have key : ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) +
      ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) + 1 ≤
      ((univ.filter fun c => ε c = ε a).card : ℝ) := by
    have h1 : ∑ c : Fin n, (if c = a then (1:ℝ) else 0) = 1 := by simp
    rw [← h1]
    simp only [numRho_cardR]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro c _
    rcases lt_trichotomy c a with h | h | h
    · simp [h, not_lt.mpr h.le, h.ne]
    · subst h
      simp
    · simp [h, not_lt.mpr h.le, h.ne']
  rw [h2]
  have habs : |((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) -
      ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ)| ≤
      ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) +
      ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

theorem abs_dot_root_rhoC_le {a b : Fin n} (hε : ε a ≠ ε b) :
    |dot (root a b) (rhoC ε)| ≤ ((n : ℝ) - 2) / 2 := by
  rw [numRho_dot_root_left]
  have ha := rhoC_bound ε a
  have hb := rhoC_bound ε b
  have hsum : ((univ.filter fun c => ε c = ε a).card : ℝ) +
      ((univ.filter fun c => ε c = ε b).card : ℝ) = n := by
    simp only [numRho_cardR]
    rw [← Finset.sum_add_distrib]
    have hc : ∀ c : Fin n,
        ((if ε c = ε a then (1:ℝ) else 0) + if ε c = ε b then (1:ℝ) else 0) = 1 := by
      intro c
      cases h1 : ε c <;> cases h2 : ε a <;> cases h3 : ε b <;> simp_all
    simp only [hc]
    simp
  rw [abs_le]
  constructor <;> linarith [le_abs_self (2 * rhoC ε a), neg_abs_le (2 * rhoC ε a),
    le_abs_self (2 * rhoC ε b), neg_abs_le (2 * rhoC ε b)]

private theorem card_opposite_sign_above_add_below_eq (ε : Fin n → Bool) (x : Fin n) :
    ((univ.filter fun c => x < c ∧ ε c ≠ ε x).card : ℝ) +
      ((univ.filter fun c => c < x ∧ ε c ≠ ε x).card : ℝ) =
      ((univ.filter fun c => ε c ≠ ε x).card : ℝ) := by
  simp only [numRho_cardR]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rcases lt_trichotomy c x with h | h | h
  · simp [h, not_lt.mpr h.le]
  · subst h
    simp
  · simp [h, not_lt.mpr h.le]

theorem dot_rhoN_root_ge {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b) :
    2 - (n : ℝ) / 2 ≤ dot (rhoN ε) (root a b) := by
  rw [numRho_dot_root_right]
  have hA := card_opposite_sign_above_add_below_eq ε a
  have hB := card_opposite_sign_above_add_below_eq ε b
  have hsum : ((univ.filter fun c => ε c ≠ ε a).card : ℝ) +
      ((univ.filter fun c => ε c ≠ ε b).card : ℝ) = n := by
    simp only [numRho_cardR]
    rw [← Finset.sum_add_distrib]
    have hc : ∀ c : Fin n,
        ((if ε c ≠ ε a then (1:ℝ) else 0) + if ε c ≠ ε b then (1:ℝ) else 0) = 1 := by
      intro c
      cases h1 : ε c <;> cases h2 : ε a <;> cases h3 : ε b <;> simp_all
    simp only [hc]
    simp
  have hUa : (1:ℝ) ≤ ((univ.filter fun c => a < c ∧ ε c ≠ ε a).card : ℝ) := by
    have h : 0 < (univ.filter fun c => a < c ∧ ε c ≠ ε a).card :=
      Finset.card_pos.mpr ⟨b, by simp [hab, Ne.symm hε]⟩
    exact_mod_cast h
  have hLb : (1:ℝ) ≤ ((univ.filter fun c => c < b ∧ ε c ≠ ε b).card : ℝ) := by
    have h : 0 < (univ.filter fun c => c < b ∧ ε c ≠ ε b).card :=
      Finset.card_pos.mpr ⟨a, by simp [hab, hε]⟩
    exact_mod_cast h
  have hra : 2 * rhoN ε a = ((univ.filter fun c => a < c ∧ ε c ≠ ε a).card : ℝ) -
      ((univ.filter fun c => c < a ∧ ε c ≠ ε a).card : ℝ) := by
    simp only [rhoN]
    ring
  have hrb : 2 * rhoN ε b = ((univ.filter fun c => b < c ∧ ε c ≠ ε b).card : ℝ) -
      ((univ.filter fun c => c < b ∧ ε c ≠ ε b).card : ℝ) := by
    simp only [rhoN]
    ring
  linarith

theorem numRho_sum_opp (ε : Fin n → Bool) :
    (∑ a, ((univ.filter fun c => ε c ≠ ε a).card : ℝ)) = 2 * (pOf ε : ℝ) * (qOf ε : ℝ) := by
  have h1 : ∀ a : Fin n, ((univ.filter fun c => ε c ≠ ε a).card : ℝ) =
      if ε a = true then (qOf ε : ℝ) else (pOf ε : ℝ) := by
    intro a
    cases h : ε a <;> simp [pOf, qOf]
  have hq : (univ.filter fun x => ¬ ε x = true).card = qOf ε := by simp [qOf]
  have hp : (univ.filter fun x => ε x = true).card = pOf ε := rfl
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    hq, hp]
  simp only [nsmul_eq_mul]
  ring

theorem two_dot_rhoC_rhoN_le (ε : Fin n → Bool) :
    2 * dot (rhoC ε) (rhoN ε) ≤ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by
  have key : ∀ a : Fin n, 2 * (rhoC ε a * rhoN ε a) ≤
      (n : ℝ) / 2 * ((univ.filter fun c => ε c ≠ ε a).card : ℝ) := by
    intro a
    have hb := rhoC_bound ε a
    have hcn : ((univ.filter fun c => ε c = ε a).card : ℝ) ≤ n := by
      have h := Finset.card_filter_le (univ : Finset (Fin n)) (fun c => ε c = ε a)
      rw [Finset.card_univ, Fintype.card_fin] at h
      exact_mod_cast h
    have hs := card_opposite_sign_above_add_below_eq ε a
    have hr : 2 * rhoN ε a = ((univ.filter fun c => a < c ∧ ε c ≠ ε a).card : ℝ) -
        ((univ.filter fun c => c < a ∧ ε c ≠ ε a).card : ℝ) := by
      simp only [rhoN]
      ring
    have hU : (0:ℝ) ≤ ((univ.filter fun c => a < c ∧ ε c ≠ ε a).card : ℝ) := Nat.cast_nonneg _
    have hL : (0:ℝ) ≤ ((univ.filter fun c => c < a ∧ ε c ≠ ε a).card : ℝ) := Nat.cast_nonneg _
    have hC : |2 * rhoC ε a| ≤ (n : ℝ) := by linarith
    have hN : |2 * rhoN ε a| ≤ ((univ.filter fun c => ε c ≠ ε a).card : ℝ) := by
      rw [hr]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have he : (2 * rhoC ε a) * (2 * rhoN ε a) ≤ |2 * rhoC ε a| * |2 * rhoN ε a| := by
      rw [← abs_mul]
      exact le_abs_self _
    have hm : |2 * rhoC ε a| * |2 * rhoN ε a| ≤
        (n : ℝ) * ((univ.filter fun c => ε c ≠ ε a).card : ℝ) :=
      mul_le_mul hC hN (abs_nonneg _) (Nat.cast_nonneg n)
    have h4 : (2 * rhoC ε a) * (2 * rhoN ε a) = 4 * (rhoC ε a * rhoN ε a) := by ring
    have h5 : (n : ℝ) / 2 * ((univ.filter fun c => ε c ≠ ε a).card : ℝ) =
        ((n : ℝ) * ((univ.filter fun c => ε c ≠ ε a).card : ℝ)) / 2 := by ring
    linarith
  rw [dot, Finset.mul_sum]
  calc ∑ a, 2 * (rhoC ε a * rhoN ε a)
      ≤ ∑ a, (n : ℝ) / 2 * ((univ.filter fun c => ε c ≠ ε a).card : ℝ) :=
        Finset.sum_le_sum (fun a _ => key a)
    _ = (n : ℝ) / 2 * ∑ a, ((univ.filter fun c => ε c ≠ ε a).card : ℝ) := by
        rw [Finset.mul_sum]
    _ = (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by
        rw [numRho_sum_opp]
        ring

theorem nsq_root {a b : Fin n} (hab : a ≠ b) : nsq (root a b) = 2 := by
  rw [nsq, numRho_dot_root_left]
  simp [root, Pi.single_apply, hab, Ne.symm hab] <;> norm_num

private theorem nsq_add_bochner_inequality (u v : Fin n → ℝ) : nsq (u + v) = nsq u + 2 * dot u v + nsq v := by
  simp only [nsq, dot, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem casValK_add (μ ν : Fin n → ℝ) :
    casValK ε (μ + ν) = casValK ε μ + 2 * dot (μ + rhoC ε) ν + nsq ν := by
  simp only [casValK]
  rw [add_right_comm μ ν (rhoC ε), nsq_add_bochner_inequality]
  ring

theorem lowK_add_rhoC (lam : Fin n → ℝ) : lowK ε lam + rhoC ε = lam + rhoN ε := by
  simp only [lowK, sub_add_cancel]

end NumRho

end ReciprocityTheory.ChartRestriction.DS
