import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.CFrob

open NumberField Filter Topology

noncomputable section

namespace PI.OkpW

theorem ultra_tail {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] (x : ℕ → E) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (h : ∀ k, ‖x (k + 1) - x k‖ ≤ r ^ (k + 1)) (k j : ℕ) :
    ‖x (j + k) - x k‖ ≤ r ^ (k + 1) := by
  induction j with
  | zero =>
    simp only [zero_add, sub_self, norm_zero]
    positivity
  | succ j ih =>
    have h1 := h (j + k)
    have h2 : ‖x (j + 1 + k) - x k‖ ≤ max ‖x (j + k + 1) - x (j + k)‖ ‖x (j + k) - x k‖ := by
      have h4 := IsUltrametricDist.norm_add_le_max (x (j + k + 1) - x (j + k)) (x (j + k) - x k)
      rw [show j + 1 + k = j + k + 1 by ring]
      simpa using h4
    have h3 : r ^ (j + k + 1) ≤ r ^ (k + 1) := pow_le_pow_of_le_one hr0 hr1 (by omega)
    exact h2.trans (max_le (h1.trans h3) ih)

theorem ultra_limit {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] [CompleteSpace E]
    (x : ℕ → E) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (h : ∀ k, ‖x (k + 1) - x k‖ ≤ r ^ (k + 1)) :
    Tendsto x atTop (𝓝 (limUnder atTop x)) ∧ ∀ k, ‖limUnder atTop x - x k‖ ≤ r ^ (k + 1) := by
  have hc : CauchySeq x := cauchySeq_of_le_geometric r r hr1 (fun n => by
    rw [dist_comm, dist_eq_norm, ← pow_succ']; exact h n)
  have ht := hc.tendsto_limUnder
  refine ⟨ht, fun k => ?_⟩
  have ht' : Tendsto (fun j => ‖x (j + k) - x k‖) atTop (𝓝 ‖limUnder atTop x - x k‖) :=
    (((tendsto_add_atTop_iff_nat k).mpr ht).sub_const (x k)).norm
  exact le_of_tendsto' ht' (fun j => ultra_tail x hr0 hr1.le h k j)

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]

theorem pinv_lt_one : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

theorem pinv_nonneg : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

def tseq (τ : K →+* ℂ_[p]) (a : 𝓞 K) (k : ℕ) : ℂ_[p] := τ ((a ^ ((p ^ 2) ^ k) : 𝓞 K) : K)

def teich (τ : K →+* ℂ_[p]) (a : 𝓞 K) : ℂ_[p] := limUnder atTop (tseq τ a)

theorem tau_pow (τ : K →+* ℂ_[p]) (x : 𝓞 K) (n : ℕ) : τ ((x ^ n : 𝓞 K) : K) = τ (x : K) ^ n := by
  simp [map_pow]

theorem tau_sub (τ : K →+* ℂ_[p]) (x y : 𝓞 K) : τ ((x - y : 𝓞 K) : K) = τ (x : K) - τ (y : K) := by
  simp [map_sub]

theorem dvd_pow_q_sub (a b : 𝓞 K) (h : (p : 𝓞 K) ∣ a - b) (k : ℕ) :
    (p : 𝓞 K) ^ (k + 1) ∣ a ^ ((p ^ 2) ^ k) - b ^ ((p ^ 2) ^ k) := by
  have h1 := dvd_sub_pow_of_dvd_sub h (2 * k)
  rw [show (p ^ 2) ^ k = p ^ (2 * k) by rw [← pow_mul]]
  exact (pow_dvd_pow _ (by omega)).trans h1

theorem tseq_step (τ : K →+* ℂ_[p]) (hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b) (a : 𝓞 K)
    (k : ℕ) : ‖tseq τ a (k + 1) - tseq τ a k‖ ≤ (p : ℝ)⁻¹ ^ (k + 1) := by
  have h1 := dvd_pow_q_sub (a ^ (p ^ 2)) a (hq a) k
  rw [← pow_mul, ← pow_succ'] at h1
  have := norm_tau_dvd τ h1
  simpa [tseq, map_sub] using this

theorem teich_spec (τ : K →+* ℂ_[p]) (hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b) (a : 𝓞 K) :
    Tendsto (tseq τ a) atTop (𝓝 (teich τ a)) ∧
      ∀ k, ‖teich τ a - tseq τ a k‖ ≤ (p : ℝ)⁻¹ ^ (k + 1) :=
  ultra_limit (tseq τ a) pinv_nonneg pinv_lt_one (tseq_step τ hq a)

theorem teich_close (τ : K →+* ℂ_[p]) (hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b) (a : 𝓞 K) :
    ‖teich τ a - τ (a : K)‖ ≤ (p : ℝ)⁻¹ := by
  have h := (teich_spec τ hq a).2 0
  simp only [tseq, pow_zero, pow_one, zero_add] at h
  exact h

theorem teich_pow (τ : K →+* ℂ_[p]) (hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b) (a : 𝓞 K) :
    teich τ a ^ (p ^ 2) = teich τ a := by
  have h1 := ((teich_spec τ hq a).1).pow (p ^ 2)
  have h2 := (tendsto_add_atTop_iff_nat 1).mpr (teich_spec τ hq a).1
  have e : (fun k => tseq τ a k ^ (p ^ 2)) = fun k => tseq τ a (k + 1) := by
    funext k
    simp only [tseq]
    rw [← tau_pow, ← pow_mul, ← pow_succ]
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2

theorem teich_c (τ : K →+* ℂ_[p]) (hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b) (a b : 𝓞 K)
    (hb : (p : 𝓞 K) ∣ b - a ^ p) : teich τ b = teich τ a ^ p := by
  have h1 := ((teich_spec τ hq a).1).pow p
  have hd : Tendsto (fun k => tseq τ b k - tseq τ a k ^ p) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun k => (p : ℝ)⁻¹ ^ k) (fun k => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one pinv_nonneg pinv_lt_one)
    have h2 := dvd_pow_q_sub b (a ^ p) hb k
    have h3 := norm_tau_dvd τ h2
    have e : tseq τ b k - tseq τ a k ^ p = τ ((b ^ ((p ^ 2) ^ k) - (a ^ p) ^ ((p ^ 2) ^ k) : 𝓞 K) : K) := by
      simp only [tseq]
      have e2 : (a ^ ((p ^ 2) ^ k)) ^ p = (a ^ p) ^ ((p ^ 2) ^ k) := pow_right_comm _ _ _
      rw [tau_sub, ← tau_pow, e2]
    rw [e]
    exact h3.trans (pow_le_pow_of_le_one pinv_nonneg pinv_lt_one.le (by omega))
  have h4 := h1.add hd
  simp only [add_sub_cancel, add_zero] at h4
  exact tendsto_nhds_unique (teich_spec τ hq b).1 h4

end PI.OkpW
