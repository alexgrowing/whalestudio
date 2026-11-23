import Mathlib

open Polynomial

private theorem pow_congr {l : ℕ} [Fact (Nat.Prime l)] {x : PadicAlgCl l} (hx : ‖x‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ ‖x ^ n - 1‖ < 1 := by
  have hint : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let F := IntermediateField.adjoin ℚ_[l] {x}
  have hF : FiniteDimensional ℚ_[l] F := IntermediateField.adjoin.finiteDimensional hint
  let V : Submodule ℚ_[l] (PadicAlgCl l) := F.toSubalgebra.toSubmodule
  have hV : FiniteDimensional ℚ_[l] V := hF
  have hP : ProperSpace V := FiniteDimensional.proper ℚ_[l] V
  have hxF : x ∈ F := IntermediateField.mem_adjoin_simple_self ℚ_[l] x
  let u : ℕ → V := fun n => ⟨x ^ n, pow_mem hxF n⟩
  have hu : ∀ n, u n ∈ Metric.closedBall (0 : V) 1 := by
    intro n
    rw [mem_closedBall_zero_iff]
    change ‖x ^ n‖ ≤ 1
    rw [norm_pow, hx, one_pow]
  obtain ⟨a, -, φ, hφ, ha⟩ := (isCompact_closedBall (0 : V) 1).tendsto_subseq hu
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 ha.cauchySeq 1 one_pos
  have h1 := hN (N + 1) (Nat.le_succ N)
  have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  refine ⟨φ (N + 1) - φ N, Nat.sub_pos_of_lt hlt, ?_⟩
  have h2 : ‖x ^ φ (N + 1) - x ^ φ N‖ < 1 := by
    rw [dist_eq_norm] at h1
    exact h1
  have h3 : x ^ φ (N + 1) - x ^ φ N = x ^ φ N * (x ^ (φ (N + 1) - φ N) - 1) := by
    rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hlt.le, mul_one]
  rwa [h3, norm_mul, norm_pow, hx, one_pow, one_mul] at h2

private theorem descend {l : ℕ} [hl : Fact (Nat.Prime l)] {y : PadicAlgCl l} (hy : ‖y‖ = 1)
    (h : ‖y ^ l - 1‖ < 1) : ‖y - 1‖ < 1 := by
  have hp : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  set z := y - 1 with hz
  have hz1 : ‖z‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max y (-1)
    rw [norm_neg, norm_one, hy, max_self, ← sub_eq_add_neg] at this
    exact this
  have hyz : y = z + 1 := by rw [hz]; ring
  have e := add_pow_prime_eq' hl.out z 1
  set S := ∑ k ∈ Finset.Ioo 0 l, z ^ k * 1 ^ (l - k) * ((l.choose k / l : ℕ) : PadicAlgCl l)
    with hS
  have hS1 : ‖S‖ ≤ 1 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro k _
    rw [one_pow, mul_one, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hz1) (norm_nonneg _)
      (IsUltrametricDist.norm_natCast_le_one _ _)
  have e2 : z ^ l = (y ^ l - 1) + -((l : PadicAlgCl l) * S) := by
    rw [hyz, e]; ring
  have h4 : ‖z ^ l‖ < 1 := by
    rw [e2]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h ?_)
    rw [norm_neg, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hp hS1
  rw [norm_pow] at h4
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h4

private theorem coprime_pow_congr {l : ℕ} [hl : Fact (Nat.Prime l)] {x : PadicAlgCl l}
    (hx : ‖x‖ = 1) : ∃ m : ℕ, ¬l ∣ m ∧ ‖x ^ m - 1‖ < 1 := by
  obtain ⟨n, hn, h⟩ := pow_congr hx
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' l hl.out.ne_one
  refine ⟨m, hm, ?_⟩
  clear hn
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply descend (by rw [norm_pow, hx, one_pow])
    rwa [← pow_mul, mul_right_comm, ← pow_succ]

theorem UpperTheory.Reformulated.B.ExistsRootCongruence.exists_root_congr :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {x : PadicAlgCl l},
    ‖x‖ = (1 : ℝ) → ∃ (m : ℕ) (ζ : PadicAlgCl l), ¬l ∣ m ∧ ζ ^ m = (1 : PadicAlgCl l) ∧ ‖x - ζ‖ < (1 : ℝ) := by
  intro l _ x hx
  obtain ⟨m, hm, h⟩ := coprime_pow_congr hx
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
  haveI : NeZero m := ⟨hm0.ne'⟩
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) m
  have e := congrArg (eval x) (X_pow_sub_one_eq_prod hm0 hμ)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at e
  by_contra hcon
  push Not at hcon
  rw [e, norm_prod] at h
  refine absurd h (not_lt.2 ?_)
  refine Finset.prod_induction _ (fun r : ℝ => 1 ≤ r)
    (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl ?_
  intro ζ hζ
  exact hcon m ζ hm ((mem_nthRootsFinset hm0 1).1 hζ)
