import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Finset

namespace BernoulliSums

variable {α : Type*} [Fintype α]

theorem bern_nonneg {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (T : Finset α) : 0 ≤ bern δ T := by
  unfold bern
  exact mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

theorem sum_bern_card (δ : ℝ) (f : ℕ → ℝ) :
    ∑ T : Finset α, bern δ T * f T.card =
      ∑ ν ∈ range (Fintype.card α + 1),
        (bernsteinPolynomial ℝ (Fintype.card α) ν).eval δ * f ν := by
  classical
  simp only [bern]
  rw [← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (fun k => δ ^ k * (1 - δ) ^ (Fintype.card α - k) * f k),
    Finset.card_univ]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp [bernsteinPolynomial, nsmul_eq_mul]
  ring

theorem sum_bern (δ : ℝ) : ∑ T : Finset α, bern δ T = 1 := by
  have h := sum_bern_card (α := α) δ (fun _ => 1)
  simp only [mul_one] at h
  rw [h, ← Polynomial.eval_finset_sum, bernsteinPolynomial.sum, Polynomial.eval_one]

theorem sum_bern_var (δ : ℝ) :
    ∑ T : Finset α, bern δ T * (((Fintype.card α : ℕ) : ℝ) * δ - T.card) ^ 2 =
      (Fintype.card α : ℝ) * δ * (1 - δ) := by
  rw [sum_bern_card δ (fun ν => (((Fintype.card α : ℕ) : ℝ) * δ - ν) ^ 2)]
  have h := congrArg (Polynomial.eval δ) (bernsteinPolynomial.variance ℝ (Fintype.card α))
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_smul, Polynomial.eval_X, Polynomial.eval_natCast,
    nsmul_eq_mul, Polynomial.eval_one] at h
  rw [← h]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

end BernoulliSums

open BernoulliSums

open Classical in
theorem branching_interlacing_pairs (D : D7) (sc : Scale) : Conclusion6 D sc := by
  intro δ hδ0 hδ1 hδn β BAD _ hbad P hp ω hP hω
  set n : ℕ := Fintype.card (HH D) with hndef
  have hn : ((n : ℕ) : ℝ) = (D.R.n : ℝ) := by
    rw [hndef]
    first
      | exact_mod_cast Formalism.HC.Frame.card_A (φ := D.R.toFrame)
      | exact_mod_cast Formalism.HC.Frame.card_A D.R.toFrame
      | (rw [Formalism.HC.Frame.card_A]; rfl)
  rw [← hn] at hδn ⊢
  have hnpos : (0 : ℝ) < n := by nlinarith
  have hbern0 : ∀ T : Finset (HH D), 0 ≤ bern δ T := fun T => bern_nonneg hδ0.le hδ1 T
  have hsum1 : ∑ T : Finset (HH D), bern δ T = 1 := sum_bern δ
  have hvar := sum_bern_var (α := HH D) δ
  rw [← hndef] at hvar
  set B : ℝ := 4 * β * δ * n * ∑ p ∈ P, ω p with hB
  by_contra hcon
  push_neg at hcon

  have hper : ∀ p ∈ P, ∑ T : Finset (HH D),
      bern δ T * ((T.filter (fun t => BAD (hp p) t T)).card : ℝ) ≤ n * (β * δ) := by
    intro p hpP
    have hc : ∀ T : Finset (HH D), bern δ T * ((T.filter (fun t => BAD (hp p) t T)).card : ℝ) =
        ∑ t : HH D, if t ∈ T ∧ BAD (hp p) t T then bern δ T else 0 := by
      intro T
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have : (Finset.univ.filter fun t => t ∈ T ∧ BAD (hp p) t T) = T.filter (fun t => BAD (hp p) t T) := by
        ext t; simp
      rw [this, mul_comm]
    calc ∑ T : Finset (HH D), bern δ T * ((T.filter (fun t => BAD (hp p) t T)).card : ℝ)
        = ∑ T : Finset (HH D), ∑ t : HH D, (if t ∈ T ∧ BAD (hp p) t T then bern δ T else 0) :=
          Finset.sum_congr rfl fun T _ => hc T
      _ = ∑ t : HH D, ∑ T : Finset (HH D), (if t ∈ T ∧ BAD (hp p) t T then bern δ T else 0) :=
          Finset.sum_comm
      _ ≤ ∑ _t : HH D, β * δ :=
          Finset.sum_le_sum fun t _ => by convert hbad (hp p) (hP p hpP) t
      _ = n * (β * δ) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  set Y : Finset (HH D) → ℝ := fun T =>
    ∑ p ∈ P, ω p * ((T.filter (fun t => BAD (hp p) t T)).card : ℝ) with hY
  have hY0 : ∀ T, 0 ≤ Y T := fun T =>
    Finset.sum_nonneg fun p hpP => mul_nonneg (hω p hpP) (Nat.cast_nonneg _)
  have hEY : ∑ T : Finset (HH D), bern δ T * Y T ≤ n * (β * δ) * ∑ p ∈ P, ω p := by
    calc ∑ T : Finset (HH D), bern δ T * Y T
        = ∑ p ∈ P, ω p * ∑ T : Finset (HH D),
            bern δ T * ((T.filter (fun t => BAD (hp p) t T)).card : ℝ) := by
          simp only [hY, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun T _ => by ring
      _ ≤ ∑ p ∈ P, ω p * (n * (β * δ)) :=
          Finset.sum_le_sum fun p hpP => mul_le_mul_of_nonneg_left (hper p hpP) (hω p hpP)
      _ = n * (β * δ) * ∑ p ∈ P, ω p := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by ring
  have hEY0 : 0 ≤ ∑ T : Finset (HH D), bern δ T * Y T :=
    Finset.sum_nonneg fun T _ => mul_nonneg (hbern0 T) (hY0 T)

  let good : Finset (HH D) → Prop := fun T => δ * n / 2 ≤ T.card ∧ (T.card : ℝ) ≤ 2 * δ * n
  have hq : 0 < (δ * n) ^ 2 := by positivity
  have hcheb : ∀ T : Finset (HH D), (if good T then (0 : ℝ) else bern δ T) ≤
      bern δ T * ((n * δ - T.card) ^ 2 * (4 / (δ * n) ^ 2)) := by
    intro T
    split_ifs with hg
    · exact mul_nonneg (hbern0 T) (mul_nonneg (sq_nonneg _) (by positivity))
    · have h1 : (δ * n) ^ 2 ≤ 4 * (n * δ - T.card) ^ 2 := by
        simp only [good, not_and_or, not_le] at hg
        rcases hg with h | h
        · nlinarith
        · nlinarith
      calc bern δ T = bern δ T * 1 := (mul_one _).symm
        _ ≤ bern δ T * ((n * δ - T.card) ^ 2 * (4 / (δ * n) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (hbern0 T)
          rw [mul_div_assoc', le_div_iff₀ hq]
          linarith
  have hbad_le : ∑ T : Finset (HH D), (if good T then (0 : ℝ) else bern δ T) ≤ 1 / 4 := by
    calc ∑ T : Finset (HH D), (if good T then (0 : ℝ) else bern δ T)
        ≤ ∑ T : Finset (HH D), bern δ T * ((n * δ - T.card) ^ 2 * (4 / (δ * n) ^ 2)) :=
          Finset.sum_le_sum fun T _ => hcheb T
      _ = (n * δ * (1 - δ)) * (4 / (δ * n) ^ 2) := by
          rw [← hvar, Finset.sum_mul]
          exact Finset.sum_congr rfl fun T _ => by ring
      _ ≤ 1 / 4 := by
          rw [mul_div_assoc', div_le_iff₀ hq]
          nlinarith [mul_le_mul_of_nonneg_left hδn (by positivity : (0 : ℝ) ≤ δ * n),
            mul_nonneg (mul_nonneg hδ0.le hδ0.le) hnpos.le]
  have hsplit : ∑ T : Finset (HH D), (if good T then bern δ T else 0) +
      ∑ T : Finset (HH D), (if good T then (0 : ℝ) else bern δ T) = 1 := by
    rw [← Finset.sum_add_distrib, ← hsum1]
    exact Finset.sum_congr rfl fun T _ => by split_ifs <;> ring
  obtain ⟨T0, -, hT0⟩ : ∃ T0 ∈ (Finset.univ : Finset (Finset (HH D))),
      (0 : ℝ) < (if good T0 then bern δ T0 else 0) := by
    by_contra hne
    push_neg at hne
    have : ∑ T : Finset (HH D), (if good T then bern δ T else 0) ≤ 0 := Finset.sum_nonpos hne
    linarith
  have hgood0 : good T0 := by
    by_contra hg
    rw [if_neg hg] at hT0
    exact lt_irrefl _ hT0
  rw [if_pos hgood0] at hT0
  have hlow : B * ∑ T : Finset (HH D), (if good T then bern δ T else 0) <
      ∑ T : Finset (HH D), bern δ T * Y T := by
    calc B * ∑ T : Finset (HH D), (if good T then bern δ T else 0)
        = ∑ T : Finset (HH D), (if good T then bern δ T * B else 0) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun T _ => by split_ifs <;> ring
      _ < ∑ T : Finset (HH D), (if good T then bern δ T * Y T else 0) := by
          apply Finset.sum_lt_sum
          · intro T _
            split_ifs with hg
            · exact mul_le_mul_of_nonneg_left (hcon T hg.1 hg.2).le (hbern0 T)
            · exact le_refl _
          · refine ⟨T0, Finset.mem_univ _, ?_⟩
            rw [if_pos hgood0, if_pos hgood0]
            exact mul_lt_mul_of_pos_left (hcon T0 hgood0.1 hgood0.2) hT0
      _ ≤ ∑ T : Finset (HH D), bern δ T * Y T := by
          apply Finset.sum_le_sum
          intro T _
          split_ifs
          · exact le_refl _
          · exact mul_nonneg (hbern0 T) (hY0 T)
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  nlinarith [mul_le_mul_of_nonneg_left (show (3 : ℝ) / 4 ≤ ∑ T : Finset (HH D), (if good T then bern δ T else 0) by linarith) hB0]

end Formalism.MainNotions.UnusedSlot33

end
