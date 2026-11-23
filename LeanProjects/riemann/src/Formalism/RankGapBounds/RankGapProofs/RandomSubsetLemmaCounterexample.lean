import Formalism.RankGapBounds.RandomSubsetCounterexample

namespace Formalism.RankGapBounds.LocalQuadraticParts

open Finset

lemma wt_nonneg {α : Type*} [Fintype α] {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (T : Finset α) :
    0 ≤ wt δ T :=
  mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

lemma sum_wt {α : Type*} [Fintype α] (δ : ℝ) : ∑ T : Finset α, wt δ T = 1 := by
  have h := Finset.sum_pow_mul_eq_add_pow δ (1 - δ) (Finset.univ : Finset α)
  rw [Finset.powerset_univ, Finset.card_univ] at h
  simp only [wt]
  rw [h]
  simp

lemma sum_wt_var {α : Type*} [Fintype α] (δ : ℝ) :
    ∑ T : Finset α, wt δ T * ((T.card : ℝ) - δ * Fintype.card α) ^ 2 =
      Fintype.card α * δ * (1 - δ) := by
  have h := congrArg (Polynomial.eval δ) (bernsteinPolynomial.variance (R := ℝ) (Fintype.card α))
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast,
    Polynomial.eval_one, bernsteinPolynomial, nsmul_eq_mul] at h
  have h2 := Finset.sum_powerset_apply_card
    (fun k : ℕ => δ ^ k * (1 - δ) ^ (Fintype.card α - k) * ((k : ℝ) - δ * Fintype.card α) ^ 2)
    (x := (Finset.univ : Finset α))
  rw [Finset.powerset_univ, Finset.card_univ] at h2
  simp only [wt]
  refine h2.trans ?_
  rw [← h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [nsmul_eq_mul]
  ring

lemma sum_wt_bad {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] (δ β : ℝ) (ω : ι → ℝ)
    (BAD : ι → α → Finset α → Prop) [∀ p t T, Decidable (BAD p t T)] (hω : ∀ p, 0 ≤ ω p)
    (hBAD : ∀ p t, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T),
      wt δ T ≤ β * δ) :
    ∑ T : Finset α, wt δ T * ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ) ≤
      β * δ * Fintype.card α * ∑ p, ω p := by
  have key : ∀ p, ∑ T : Finset α, wt δ T * ((T.filter fun t => BAD p t T).card : ℝ) ≤
      β * δ * Fintype.card α := by
    intro p
    have e : ∀ T : Finset α, wt δ T * ((T.filter fun t => BAD p t T).card : ℝ) =
        ∑ t : α, if t ∈ T ∧ BAD p t T then wt δ T else 0 := by
      intro T
      have hf : (Finset.univ : Finset α).filter (fun t => t ∈ T ∧ BAD p t T) =
          T.filter fun t => BAD p t T := by
        ext t; simp
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hf, mul_comm]
    calc ∑ T : Finset α, wt δ T * ((T.filter fun t => BAD p t T).card : ℝ)
        = ∑ T : Finset α, ∑ t : α, (if t ∈ T ∧ BAD p t T then wt δ T else 0) :=
          Finset.sum_congr rfl (fun T _ => e T)
      _ = ∑ t : α, ∑ T : Finset α, (if t ∈ T ∧ BAD p t T then wt δ T else 0) := Finset.sum_comm
      _ = ∑ t : α, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T),
            wt δ T := by
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [Finset.sum_filter]
      _ ≤ ∑ _t : α, β * δ := Finset.sum_le_sum (fun t _ => hBAD p t)
      _ = β * δ * Fintype.card α := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  calc ∑ T : Finset α, wt δ T * ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ)
      = ∑ p, ω p * ∑ T : Finset α, wt δ T * ((T.filter fun t => BAD p t T).card : ℝ) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun T _ => ?_))
        ring
    _ ≤ ∑ p, ω p * (β * δ * Fintype.card α) :=
        Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (key p) (hω p))
    _ = β * δ * Fintype.card α * ∑ p, ω p := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)

lemma pick {γ : Type*} (s : Finset γ) (w V X : γ → ℝ) (r M : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (hw : ∀ T ∈ s, 0 ≤ w T) (hsum : ∑ T ∈ s, w T = 1) (hV0 : ∀ T ∈ s, 0 ≤ V T)
    (hV : ∑ T ∈ s, w T * V T ≤ 2 / 3 * r) (hX0 : ∀ T ∈ s, 0 ≤ X T)
    (hXs : ∑ T ∈ s, w T * X T ≤ M) :
    ∃ T ∈ s, V T < r ∧ X T ≤ 4 * M := by
  by_contra hcon
  push Not at hcon
  have hG : ∑ T ∈ s.filter (fun T => ¬ 4 * M < X T), w T ≤ 2 / 3 := by
    have hle : ∀ T ∈ s.filter (fun T => ¬ 4 * M < X T), w T ≤ w T * V T / r := by
      intro T hT
      rw [Finset.mem_filter] at hT
      have hVT : r ≤ V T := by
        by_contra h
        push Not at h
        exact hT.2 (hcon T hT.1 h)
      rw [le_div_iff₀ hr]
      exact mul_le_mul_of_nonneg_left hVT (hw T hT.1)
    calc ∑ T ∈ s.filter (fun T => ¬ 4 * M < X T), w T
        ≤ ∑ T ∈ s.filter (fun T => ¬ 4 * M < X T), w T * V T / r := Finset.sum_le_sum hle
      _ = (∑ T ∈ s.filter (fun T => ¬ 4 * M < X T), w T * V T) / r := by rw [Finset.sum_div]
      _ ≤ (∑ T ∈ s, w T * V T) / r := by
          apply div_le_div_of_nonneg_right _ hr.le
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro T hT _
          exact mul_nonneg (hw T hT) (hV0 T hT)
      _ ≤ (2 / 3 * r) / r := div_le_div_of_nonneg_right hV hr.le
      _ = 2 / 3 := by field_simp
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun T => 4 * M < X T) w
  have hB : 1 / 3 ≤ ∑ T ∈ s.filter (fun T => 4 * M < X T), w T := by linarith
  obtain ⟨T0, hT0, hwT0⟩ : ∃ T ∈ s.filter (fun T => 4 * M < X T), 0 < w T := by
    by_contra h
    push Not at h
    have : ∑ T ∈ s.filter (fun T => 4 * M < X T), w T ≤ 0 := Finset.sum_nonpos h
    linarith
  have hlt : ∑ T ∈ s.filter (fun T => 4 * M < X T), w T * (4 * M) <
      ∑ T ∈ s.filter (fun T => 4 * M < X T), w T * X T := by
    apply Finset.sum_lt_sum
    · intro T hT
      rw [Finset.mem_filter] at hT
      exact mul_le_mul_of_nonneg_left hT.2.le (hw T hT.1)
    · refine ⟨T0, hT0, ?_⟩
      rw [Finset.mem_filter] at hT0
      exact mul_lt_mul_of_pos_left hT0.2 hwT0
  have hsub : ∑ T ∈ s.filter (fun T => 4 * M < X T), w T * X T ≤ ∑ T ∈ s, w T * X T := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro T hT _
    exact mul_nonneg (hw T hT) (hX0 T hT)
  rw [← Finset.sum_mul] at hlt
  nlinarith [mul_nonneg (sub_nonneg.mpr hB) hM]

theorem tops_lemma_six_holds : TopsFixed := by
  intro α ι _ _ _ δ β ω BAD _ hδ0 hδ1 hq hβ hω hBAD
  have hS : 0 ≤ ∑ p, ω p := Finset.sum_nonneg fun p _ => hω p
  have hN : 0 ≤ (Fintype.card α : ℝ) := Nat.cast_nonneg _
  have hqpos : 0 < δ * Fintype.card α := by linarith
  obtain ⟨T, -, hVT, hXT⟩ := pick (Finset.univ : Finset (Finset α)) (wt δ)
    (fun T => ((T.card : ℝ) - δ * Fintype.card α) ^ 2)
    (fun T => ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ))
    ((δ * Fintype.card α / 2) ^ 2) (β * δ * Fintype.card α * ∑ p, ω p)
    (by positivity) (by positivity)
    (fun T _ => wt_nonneg hδ0.le hδ1 T) (sum_wt δ) (fun T _ => sq_nonneg _)
    (by
      rw [sum_wt_var δ]
      nlinarith [mul_nonneg hqpos.le hδ0.le,
        mul_nonneg hqpos.le (by linarith : (0 : ℝ) ≤ δ * Fintype.card α - 6)])
    (fun T _ => Finset.sum_nonneg fun p _ => mul_nonneg (hω p) (Nat.cast_nonneg _))
    (sum_wt_bad δ β ω BAD hω hBAD)
  have hab := abs_lt_of_sq_lt_sq' hVT (by positivity)
  refine ⟨T, by linarith [hab.1], by linarith [hab.2], by linarith⟩

end Formalism.RankGapBounds.LocalQuadraticParts
