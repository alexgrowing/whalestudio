import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset

theorem dominant_antitone (d : IndexData) (u : Weight d) (hu : IsDominant d u) (τ : Fin d.f) :
    ∀ i l : Fin d.N, i.val ≤ l.val → u (τ, l) ≤ u (τ, i) := by
  have key : ∀ k : ℕ, ∀ i l : Fin d.N, l.val = i.val + k → u (τ, l) ≤ u (τ, i) := by
    intro k
    induction k with
    | zero =>
      intro i l h
      have : l = i := Fin.ext (by omega)
      rw [this]
    | succ k ih =>
      intro i l h
      have hm : i.val + k < d.N := by have := l.isLt; omega
      let m : Fin d.N := ⟨i.val + k, hm⟩
      have h1 : u (τ, l) ≤ u (τ, m) := by
        have := hu τ m l (by simp [m]; omega)
        linarith
      have h2 : u (τ, m) ≤ u (τ, i) := ih i m rfl
      linarith
  intro i l h
  exact key (l.val - i.val) i l (by omega)

theorem CBounds.proof : CBounds.Statement := by
  intro d u hu τ

  set S : ℝ := ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), u (τ, i) with hS
  set T : ℝ := ∑ i ∈ univ.filter (fun i : Fin d.N => ¬ i.val < d.j), u (τ, i) with hT
  set P : ℝ := ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), |u (τ, i)| with hP
  set R : ℝ := ∑ i ∈ univ.filter (fun i : Fin d.N => ¬ i.val < d.j), |u (τ, i)| with hR
  have hsum : ∑ i : Fin d.N, u (τ, i) = S + T :=
    (sum_filter_add_sum_filter_not univ (fun i : Fin d.N => i.val < d.j) _).symm
  have habs : ∑ i : Fin d.N, |u (τ, i)| = P + R :=
    (sum_filter_add_sum_filter_not univ (fun i : Fin d.N => i.val < d.j) _).symm
  have hN : (0 : ℝ) < d.N := by have := d.two_le_N; positivity
  have hjN : (d.j : ℝ) ≤ d.N := by exact_mod_cast d.j_lt_N.le
  have hj0 : (0 : ℝ) ≤ d.j := by positivity

  have hcard1 : ((univ.filter (fun i : Fin d.N => i.val < d.j)).card : ℝ) = d.j := by
    have := Fin.card_filter_val_lt (n := d.N) (m := d.j)
    rw [this, min_eq_right d.j_lt_N.le]
  have hcard2 : ((univ.filter (fun i : Fin d.N => ¬ i.val < d.j)).card : ℝ) = d.N - d.j := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin d.N)))
      (fun i : Fin d.N => i.val < d.j)
    rw [card_univ, Fintype.card_fin] at h
    have h' : ((univ.filter (fun i : Fin d.N => i.val < d.j)).card : ℝ) +
        ((univ.filter (fun i : Fin d.N => ¬ i.val < d.j)).card : ℝ) = d.N := by
      exact_mod_cast h
    linarith
  have hc : cTau d u τ = S - (d.j : ℝ) * ((1 / (d.N : ℝ)) * (S + T)) := by
    simp only [cTau, ubar, hsum]
    rfl

  have hSP : S ≤ P := sum_le_sum (fun i _ => le_abs_self _)
  have hTR : -T ≤ R := by
    rw [hT, ← sum_neg_distrib]
    exact sum_le_sum (fun i _ => neg_le_abs _)
  have hP0 : 0 ≤ P := sum_nonneg (fun i _ => abs_nonneg _)
  have hR0 : 0 ≤ R := sum_nonneg (fun i _ => abs_nonneg _)
  set r : ℝ := (d.j : ℝ) * (1 / (d.N : ℝ)) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hr, mul_one_div, div_le_one hN]; exact hjN
  have hc' : cTau d u τ = (1 - r) * S - r * T := by rw [hc, hr]; ring
  refine ⟨?_, ?_⟩
  ·
    let v : Fin d.N := ⟨d.j, d.j_lt_N⟩
    have hmono := dominant_antitone d u hu τ
    have hS1 : (d.j : ℝ) * u (τ, v) ≤ S := by
      rw [← hcard1, ← nsmul_eq_mul, ← sum_const]
      refine sum_le_sum (fun i hi => ?_)
      have hi' : i.val < d.j := (mem_filter.mp hi).2
      exact hmono i v (by simp [v]; omega)
    have hT1 : T ≤ ((d.N : ℝ) - d.j) * u (τ, v) := by
      rw [← hcard2, ← nsmul_eq_mul, ← sum_const]
      refine sum_le_sum (fun i hi => ?_)
      have hi' : ¬ i.val < d.j := (mem_filter.mp hi).2
      exact hmono v i (by simp [v]; omega)
    have hNc : (d.N : ℝ) * cTau d u τ = ((d.N : ℝ) - d.j) * S - (d.j : ℝ) * T := by
      rw [hc]; field_simp; ring
    have h0 : 0 ≤ ((d.N : ℝ) - d.j) * S - (d.j : ℝ) * T := by
      have hNj : 0 ≤ (d.N : ℝ) - d.j := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hS1 hNj, mul_le_mul_of_nonneg_left hT1 hj0]
    rw [← hNc] at h0
    by_contra hneg
    have hneg' : cTau d u τ < 0 := lt_of_not_ge hneg
    linarith [mul_neg_of_pos_of_neg hN hneg']
  · rw [hc', habs]
    nlinarith [mul_le_mul_of_nonneg_left hSP (by linarith : (0 : ℝ) ≤ 1 - r),
      mul_le_mul_of_nonneg_left hTR hr0, mul_nonneg hr0 hP0, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - r) hR0]

end GroundTheory.Heights₂.Heights.TheoremB
