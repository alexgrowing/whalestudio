import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega

noncomputable section

namespace GlobalTheory.Honda.TwistedDivision

variable {K : Type} [NormedField K]

theorem norm_sub_le_max_of_ultrametric_field [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max x (-y)).trans_eq (by rw [norm_neg])

theorem norm_pow_apply (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) :
    ‖(τ ^ i) x‖ = ‖x‖ := by
  induction i generalizing x with
  | zero => simp
  | succ i ih => rw [pow_succ, RingHom.mul_def, RingHom.comp_apply, ih, hτ]

noncomputable def step (τ : K →+* K) (π : K) (c : ℕ → K) (t : ℕ → K) : ℕ → K
  | 0 => 1
  | m + 1 => (π * t (m + 2) - ∑ i : Fin (m + 1), step τ π c t i * (τ ^ (i : ℕ)) (c (m + 1 - i))) /
      (τ ^ (m + 1)) (c 0)
termination_by m => m
decreasing_by exact i.isLt

theorem step_zero (τ : K →+* K) (π : K) (c : ℕ → K) (t : ℕ → K) : step τ π c t 0 = 1 := by
  rw [step]

theorem step_succ (τ : K →+* K) (π : K) (c : ℕ → K) (t : ℕ → K) (m : ℕ) :
    step τ π c t (m + 1) = (π * t (m + 2) - ∑ i ∈ Finset.range (m + 1), step τ π c t i * (τ ^ i) (c (m + 1 - i))) /
      (τ ^ (m + 1)) (c 0) := by
  rw [step, Fin.sum_univ_eq_sum_range (fun i => step τ π c t i * (τ ^ i) (c (m + 1 - i)))]

variable (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (π : K) (c : ℕ → K) (hc0 : ‖c 0‖ = 1) (hc : ∀ i, ‖c i‖ ≤ 1)
include hτ hc0

include hc in
theorem step_bound [IsUltrametricDist K] (hπ : ‖π‖ ≤ 1) (t : ℕ → K) (ht : ∀ j, ‖t j‖ ≤ 1) (m : ℕ) : ‖step τ π c t m‖ ≤ 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => simp [step_zero]
    | succ m =>
      rw [step_succ, norm_div, norm_pow_apply τ hτ, hc0, div_one]
      refine (norm_sub_le_max_of_ultrametric_field _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]; exact mul_le_one₀ hπ (norm_nonneg _) (ht _)
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i hi => ?_
        rw [norm_mul, norm_pow_apply τ hτ]
        exact mul_le_one₀ (ih i (Finset.mem_range.1 hi)) (norm_nonneg _) (hc _)

include hc in
theorem step_diff [IsUltrametricDist K] (t t' : ℕ → K) (ε : ℝ) (hε : 0 ≤ ε) (h : ∀ j, ‖t j - t' j‖ ≤ ε) (m : ℕ) :
    ‖step τ π c t m - step τ π c t' m‖ ≤ ‖π‖ * ε := by
  have hπε : 0 ≤ ‖π‖ * ε := mul_nonneg (norm_nonneg _) hε
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => simpa [step_zero] using hπε
    | succ m =>
      rw [step_succ, step_succ, ← sub_div, norm_div, norm_pow_apply τ hτ, hc0, div_one]
      have key : (π * t (m + 2) - ∑ i ∈ Finset.range (m + 1), step τ π c t i * (τ ^ i) (c (m + 1 - i))) -
          (π * t' (m + 2) - ∑ i ∈ Finset.range (m + 1), step τ π c t' i * (τ ^ i) (c (m + 1 - i))) =
          π * (t (m + 2) - t' (m + 2)) -
            ∑ i ∈ Finset.range (m + 1), (step τ π c t i - step τ π c t' i) * (τ ^ i) (c (m + 1 - i)) := by
        simp only [sub_mul, Finset.sum_sub_distrib]; ring
      rw [key]
      refine (norm_sub_le_max_of_ultrametric_field _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (h _) (norm_nonneg _)
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hπε fun i hi => ?_
        rw [norm_mul, norm_pow_apply τ hτ]
        have hi' : i < m + 1 := Finset.mem_range.1 hi
        calc ‖step τ π c t i - step τ π c t' i‖ * ‖c (m + 1 - i)‖ ≤ (‖π‖ * ε) * 1 :=
              mul_le_mul (ih i hi') (hc _) (norm_nonneg _) hπε
          _ = ‖π‖ * ε := mul_one _

theorem step_eq (t : ℕ → K) (m : ℕ) :
    π * t (m + 2) = ∑ i ∈ Finset.range (m + 2), step τ π c t i * (τ ^ i) (c (m + 2 - 1 - i)) := by
  have hu : (τ ^ (m + 1)) (c 0) ≠ 0 := by
    intro h0; have := norm_pow_apply τ hτ (m + 1) (c 0); rw [h0, norm_zero, hc0] at this; exact zero_ne_one this
  rw [Finset.sum_range_succ, step_succ]
  have h1 : m + 2 - 1 - (m + 1) = 0 := by omega
  rw [h1, div_mul_cancel₀ _ hu]
  have h2 : ∑ i ∈ Finset.range (m + 1), step τ π c t i * (τ ^ i) (c (m + 2 - 1 - i)) =
      ∑ i ∈ Finset.range (m + 1), step τ π c t i * (τ ^ i) (c (m + 1 - i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have : m + 2 - 1 - i = m + 1 - i := by omega
    rw [this]
  rw [h2]; ring

end GlobalTheory.Honda.TwistedDivision

namespace GlobalTheory.Honda

open PowerSeries Filter Topology

theorem exists_twisted_division : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (τ : K →+* K),
    (∀ x, ‖τ x‖ = ‖x‖) → ∀ π : K, ‖π‖ < 1 → ∀ c : ℕ → K, ‖c 0‖ = 1 → (∀ i, ‖c i‖ ≤ 1) →
    ∃ t : ℕ → K, t 0 = 1 ∧ (∀ n, ‖t n‖ ≤ 1) ∧
      ∀ n, 2 ≤ n → π * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i)) := by
  intro K _ _ _ τ hτ π hπ c hc0 hc
  let T : ℕ → ℕ → K := fun k => (TwistedDivision.step τ π c)^[k] (fun _ => 1)
  have hTs : ∀ k, T (k + 1) = TwistedDivision.step τ π c (T k) := fun k =>
    Function.iterate_succ_apply' _ _ _
  have hπ1 : ‖π‖ ≤ 1 := hπ.le
  have hB : ∀ k j, ‖T k j‖ ≤ 1 := by
    intro k
    induction k with
    | zero => intro j; simp [T]
    | succ k ih => intro j; rw [hTs]; exact TwistedDivision.step_bound τ hτ π c hc0 hc hπ1 _ ih j
  have hD : ∀ k j, ‖T (k + 1) j - T k j‖ ≤ ‖π‖ ^ k := by
    intro k
    induction k with
    | zero => intro j; simpa using (TwistedDivision.norm_sub_le_max_of_ultrametric_field _ _).trans (max_le (hB 1 j) (hB 0 j))
    | succ k ih =>
      intro j
      have := TwistedDivision.step_diff τ hτ π c hc0 hc (T (k + 1)) (T k) _ (pow_nonneg (norm_nonneg _) _) ih j
      rw [← hTs (k + 1), ← hTs k, ← pow_succ'] at this
      exact this
  have hC : ∀ j, ∃ x, Tendsto (fun k => T k j) atTop (𝓝 x) := fun j =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric ‖π‖ 1 hπ fun k => by
      rw [dist_eq_norm, norm_sub_rev, one_mul]; exact hD k j)
  choose t ht using hC
  refine ⟨t, ?_, ?_, ?_⟩
  · have h0 : ∀ k, T k 0 = 1 := by
      intro k; cases k with
      | zero => rfl
      | succ k => rw [hTs]; exact TwistedDivision.step_zero _ _ _ _
    have : Tendsto (fun k => T k 0) atTop (𝓝 1) := by simp only [h0]; exact tendsto_const_nhds
    exact tendsto_nhds_unique (ht 0) this
  · intro j
    exact le_of_tendsto' (ht j).norm fun k => hB k j
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hL : Tendsto (fun k => π * T k (m + 2)) atTop (𝓝 (π * t (m + 2))) := (ht _).const_mul π
    have hR : Tendsto (fun k => ∑ i ∈ Finset.range (m + 2), T (k + 1) i * (τ ^ i) (c (m + 2 - 1 - i))) atTop
        (𝓝 (∑ i ∈ Finset.range (m + 2), t i * (τ ^ i) (c (m + 2 - 1 - i)))) :=
      tendsto_finsetSum _ fun i _ => (((ht i).comp (tendsto_add_atTop_nat 1)).mul_const _)
    have hEq : (fun k => π * T k (m + 2)) =
        fun k => ∑ i ∈ Finset.range (m + 2), T (k + 1) i * (τ ^ i) (c (m + 2 - 1 - i)) := by
      funext k; rw [hTs]; exact TwistedDivision.step_eq τ hτ π c hc0 _ m
    rw [hEq] at hL
    exact tendsto_nhds_unique hL hR

end GlobalTheory.Honda
