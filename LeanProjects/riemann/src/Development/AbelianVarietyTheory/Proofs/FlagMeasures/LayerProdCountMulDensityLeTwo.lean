import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open GlobalTheory.Count Finset

namespace GlobalTheory.Count

theorem layerProd_mul_layerProd (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) (G H : ℝ → ℝ) :
    layerProd n f j τ G * layerProd n f j τ H = layerProd n f j τ (fun la => G la * H la) := by
  simp only [layerProd, mul_pow, Finset.prod_mul_distrib]
  ring

private theorem layerProd_const_eq_pow (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) (c : ℝ) :
    layerProd n f j τ (fun _ => c) = c ^ (∑ i, ∑ k ∈ univ.filter (fun k => i < k),
      (2 * j i * j k * f + 2 * j i * j k * f) + ∑ i, (2 * j i * (n - 2 * ∑ l, j l) * f + j i ^ 2 * f)) := by
  simp only [layerProd, ← pow_add, Finset.prod_pow_eq_pow_sum]

private theorem layerProd_exponent_le_three_mul_sum_mul (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (hn : 2 * ∑ i, j i ≤ n) :
    ∑ i, ∑ k ∈ univ.filter (fun k => i < k), (2 * j i * j k * f + 2 * j i * j k * f) +
      ∑ i, (2 * j i * (n - 2 * ∑ l, j l) * f + j i ^ 2 * f) ≤ 3 * (∑ i, j i) * n * f := by
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ i, j i := ⟨_, rfl⟩
  rw [← hS] at hn ⊢
  have h1 : ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k ≤ S * S := by
    calc ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k ≤ ∑ i, ∑ k, j i * j k :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = S * S := by rw [hS, Finset.sum_mul_sum]
  have h2 : ∑ i, j i ^ 2 ≤ S * S := by
    calc ∑ i, j i ^ 2 ≤ ∑ i, j i * S := Finset.sum_le_sum fun i _ => by
          rw [sq, hS]
          exact Nat.mul_le_mul_left _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      _ = S * S := by rw [← Finset.sum_mul, hS]
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * S + m := ⟨n - 2 * S, by omega⟩
  have hm : 2 * S + m - 2 * S = m := by omega
  have e1 : ∑ i, ∑ k ∈ univ.filter (fun k => i < k), (2 * j i * j k * f + 2 * j i * j k * f) =
      4 * f * ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ i, (2 * j i * m * f + j i ^ 2 * f) = 2 * m * f * S + f * ∑ i, j i ^ 2 := by
    rw [hS, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hm, e1, e2]
  nlinarith [Nat.mul_le_mul_left f h1, Nat.mul_le_mul_left f h2, Nat.zero_le (S * m * f)]

theorem layerProd_le_exp (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) (G : ℝ → ℝ) (x : ℝ)
    (hx : 0 ≤ x) (hn : 2 * ∑ i, j i ≤ n) (hτ : StrictMono τ) (h01 : ∀ i, 0 < τ i ∧ τ i < 1)
    (hG : ∀ la, 0 < la → la < 1 → 0 ≤ G la ∧ G la ≤ Real.exp x) :
    layerProd n f j τ G ≤ Real.exp (((3 * (∑ i, j i) * n * f : ℕ) : ℝ) * x) := by
  have hpos : ∀ i, 0 < τ i := fun i => (h01 i).1
  have hlt : ∀ i, τ i < 1 := fun i => (h01 i).2
  have hb : ∀ la, 0 < la → la < 1 → ∀ e : ℕ, 0 ≤ G la ^ e ∧ G la ^ e ≤ Real.exp x ^ e :=
    fun la h0 h1 e => ⟨pow_nonneg (hG la h0 h1).1 e, pow_le_pow_left₀ (hG la h0 h1).1 (hG la h0 h1).2 e⟩
  have hr : ∀ i k, i < k → 0 < τ i / τ k ∧ τ i / τ k < 1 :=
    fun i k hik => ⟨div_pos (hpos i) (hpos k), (div_lt_one (hpos k)).2 (hτ hik)⟩
  have hp : ∀ i k, 0 < τ i * τ k ∧ τ i * τ k < 1 := fun i k =>
    ⟨mul_pos (hpos i) (hpos k), by nlinarith [hpos i, hpos k, hlt i, hlt k]⟩
  have hs : ∀ i, 0 < τ i ^ 2 ∧ τ i ^ 2 < 1 := fun i => ⟨pow_pos (hpos i) 2, by nlinarith [hpos i, hlt i]⟩
  have hex : 0 ≤ Real.exp x := (Real.exp_pos x).le
  have key : layerProd n f j τ G ≤ layerProd n f j τ (fun _ => Real.exp x) := by
    simp only [layerProd]
    apply mul_le_mul
    · apply Finset.prod_le_prod
      · intro i _
        apply Finset.prod_nonneg
        intro k hk
        have hik := (Finset.mem_filter.1 hk).2
        exact mul_nonneg (hb _ (hr i k hik).1 (hr i k hik).2 _).1 (hb _ (hp i k).1 (hp i k).2 _).1
      · intro i _
        apply Finset.prod_le_prod
        · intro k hk
          have hik := (Finset.mem_filter.1 hk).2
          exact mul_nonneg (hb _ (hr i k hik).1 (hr i k hik).2 _).1 (hb _ (hp i k).1 (hp i k).2 _).1
        · intro k hk
          have hik := (Finset.mem_filter.1 hk).2
          exact mul_le_mul (hb _ (hr i k hik).1 (hr i k hik).2 _).2 (hb _ (hp i k).1 (hp i k).2 _).2
            (hb _ (hp i k).1 (hp i k).2 _).1 (pow_nonneg hex _)
    · apply Finset.prod_le_prod
      · intro i _
        exact mul_nonneg (hb _ (hpos i) (hlt i) _).1 (hb _ (hs i).1 (hs i).2 _).1
      · intro i _
        exact mul_le_mul (hb _ (hpos i) (hlt i) _).2 (hb _ (hs i).1 (hs i).2 _).2
          (hb _ (hs i).1 (hs i).2 _).1 (pow_nonneg hex _)
    · apply Finset.prod_nonneg
      intro i _
      exact mul_nonneg (hb _ (hpos i) (hlt i) _).1 (hb _ (hs i).1 (hs i).2 _).1
    · apply Finset.prod_nonneg
      intro i _
      apply Finset.prod_nonneg
      intro k _
      positivity
  refine key.trans ?_
  rw [layerProd_const_eq_pow, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  apply mul_le_mul_of_nonneg_right _ hx
  exact_mod_cast layerProd_exponent_le_three_mul_sum_mul n f j hn

private theorem mul_prod_mul_le_prod_of_le_one {a : ℕ} (X : ℝ) (u v : Fin a → ℝ) (hX0 : 0 ≤ X) (hX1 : X ≤ 1)
    (hu : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) :
    X * ∏ i, u i * v i ≤ ∏ i, u i := by
  rw [Finset.prod_mul_distrib]
  have hA : 0 ≤ ∏ i, u i := Finset.prod_nonneg fun i _ => hu i
  have hB0 : 0 ≤ ∏ i, v i := Finset.prod_nonneg fun i _ => hv0 i
  have hB1 : ∏ i, v i ≤ 1 := Finset.prod_le_one (fun i _ => hv0 i) (fun i _ => hv1 i)
  calc X * ((∏ i, u i) * ∏ i, v i) ≤ 1 * ((∏ i, u i) * ∏ i, v i) :=
        mul_le_mul_of_nonneg_right hX1 (mul_nonneg hA hB0)
    _ ≤ ∏ i, u i := by rw [one_mul]; exact mul_le_of_le_one_right hA hB1

theorem layerProd_count_mul_density_le_two :
    ∀ (n f q a : ℕ) (j : Fin a → ℕ) (τ : Fin a → ℝ) (de : ℝ), ∑ i, j i ≤ q → 2 * q ≤ n → StrictMono τ →
      (∀ i, 0 < τ i ∧ τ i < 1 / 2) → 0 ≤ de → de * q * n * f ≤ 1 / 100 →
      layerProd n f j τ (fun la => 1 + 12 * de / la) * layerProd n f j τ (fun la => la) ≤ 2 ∧
      layerProd n f j τ (fun la => la) ≤ ∏ i, τ i ^ (2 * j i * (n - 2 * ∑ l, j l) * f) := by
  intro n f q a j τ de hq hqn hτ h01 hde hsmall
  have hS2 : 2 * ∑ i, j i ≤ n := by omega
  have hpos : ∀ i, 0 < τ i := fun i => (h01 i).1
  have hlt : ∀ i, τ i < 1 := fun i => by linarith [(h01 i).2]
  constructor
  · rw [layerProd_mul_layerProd]
    have hb := layerProd_le_exp n f j τ (fun la => (1 + 12 * de / la) * la) (12 * de) (by positivity)
      hS2 hτ (fun i => ⟨hpos i, hlt i⟩) (fun la h0 h1 => by
        show 0 ≤ (1 + 12 * de / la) * la ∧ (1 + 12 * de / la) * la ≤ Real.exp (12 * de)
        rw [add_mul, div_mul_cancel₀ _ h0.ne', one_mul]
        exact ⟨by linarith, by linarith [Real.add_one_le_exp (12 * de)]⟩)
    refine hb.trans ?_
    have hnat : 3 * (∑ i, j i) * n * f ≤ 3 * q * n * f := by gcongr
    have hcast : ((3 * (∑ i, j i) * n * f : ℕ) : ℝ) ≤ 3 * q * n * f := by exact_mod_cast hnat
    have hexp : ((3 * (∑ i, j i) * n * f : ℕ) : ℝ) * (12 * de) ≤ 36 / 100 := by
      calc ((3 * (∑ i, j i) * n * f : ℕ) : ℝ) * (12 * de) ≤ (3 * q * n * f : ℝ) * (12 * de) :=
            mul_le_mul_of_nonneg_right hcast (by positivity)
        _ = 36 * (de * q * n * f) := by ring
        _ ≤ 36 / 100 := by linarith
    calc Real.exp (((3 * (∑ i, j i) * n * f : ℕ) : ℝ) * (12 * de)) ≤ Real.exp (36 / 100) :=
          Real.exp_le_exp.2 hexp
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (by linarith [Real.log_two_gt_d9])
      _ = 2 := Real.exp_log (by norm_num)
  · unfold layerProd
    refine mul_prod_mul_le_prod_of_le_one _ (fun i => τ i ^ (2 * j i * (n - 2 * ∑ l, j l) * f))
      (fun i => (τ i ^ 2) ^ (j i ^ 2 * f)) ?_ ?_ (fun i => pow_nonneg (hpos i).le _)
      (fun i => pow_nonneg (pow_pos (hpos i) 2).le _) ?_
    · apply Finset.prod_nonneg
      intro i _
      apply Finset.prod_nonneg
      intro k _
      exact mul_nonneg (pow_nonneg (div_pos (hpos i) (hpos k)).le _) (pow_nonneg (mul_pos (hpos i) (hpos k)).le _)
    · apply Finset.prod_le_one
      · intro i _
        apply Finset.prod_nonneg
        intro k _
        exact mul_nonneg (pow_nonneg (div_pos (hpos i) (hpos k)).le _) (pow_nonneg (mul_pos (hpos i) (hpos k)).le _)
      · intro i _
        apply Finset.prod_le_one
        · intro k _
          exact mul_nonneg (pow_nonneg (div_pos (hpos i) (hpos k)).le _) (pow_nonneg (mul_pos (hpos i) (hpos k)).le _)
        · intro k hk
          have hik := (Finset.mem_filter.1 hk).2
          have hq1 : τ i / τ k ≤ 1 := ((div_lt_one (hpos k)).2 (hτ hik)).le
          have hp1 : τ i * τ k ≤ 1 := by nlinarith [hpos i, hpos k, hlt i, hlt k]
          exact mul_le_one₀ (pow_le_one₀ (div_pos (hpos i) (hpos k)).le hq1)
            (pow_nonneg (mul_pos (hpos i) (hpos k)).le _) (pow_le_one₀ (mul_pos (hpos i) (hpos k)).le hp1)
    · intro i
      have : τ i ^ 2 ≤ 1 := by nlinarith [hpos i, hlt i]
      exact pow_le_one₀ (pow_pos (hpos i) 2).le this

end GlobalTheory.Count
