import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

variable {L : Type} [Field L]

theorem approxRoot_exists_val_pow {p : ℕ} {v : Valuation L ℝ≥0} {F : Subfield L}
    (hA : ApproxRoot p v F) {u : L} (hu : u ∈ F) (hu0 : u ≠ 0) :
    ∃ w ∈ F, v w ^ p = v u := by
  obtain ⟨θ, hθ, h⟩ := hA
  obtain ⟨w, hw, hle⟩ := h u hu
  have hvu : 0 < v u := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hu0)
  have hlt : v (w ^ p - u) < v u := by
    rw [Valuation.map_sub_swap]
    exact lt_of_le_of_lt hle (mul_lt_of_lt_one_left hvu hθ)
  refine ⟨w, hw, ?_⟩
  rw [← map_pow]
  exact Valuation.map_eq_of_sub_lt v hlt

theorem approxRoot_exists_root_of_p {p : ℕ} (hp : p.Prime) {v : Valuation L ℝ≥0} {F : Subfield L}
    (hA : ApproxRoot p v F) (hp0 : 0 < v (p : L)) :
    ∀ k : ℕ, ∃ π ∈ F, v π ^ (p ^ k) = v (p : L) := by
  intro k
  induction k with
  | zero => exact ⟨(p : L), natCast_mem F p, by simp⟩
  | succ k ih =>
    obtain ⟨π, hπ, hv⟩ := ih
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_pow (pow_ne_zero _ hp.ne_zero)] at hv
      exact hp0.ne hv
    obtain ⟨w, hw, hw'⟩ := approxRoot_exists_val_pow hA hπ hπ0
    refine ⟨w, hw, ?_⟩
    rw [pow_succ', pow_mul, hw', hv]

theorem exists_scale_shell (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ) (hp : p.Prime)
    (F : Subfield L) (hA : ApproxRoot p v F) (hp0 : 0 < v (p : L)) (hp1 : v (p : L) < 1)
    (r : ℝ≥0) (hr : r < 1) (x : L) (hx : x ≠ 0) :
    ∃ d ∈ F, d ≠ 0 ∧ r < v (x * d ^ p) ∧ v (x * d ^ p) ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (pow_pos hp0 p) hr
  obtain ⟨π, hπ, hv⟩ := approxRoot_exists_root_of_p hp hA hp0 n
  set s := v π with hs
  set t := s ^ p with ht
  have hrt : r < t := by
    by_contra h
    push_neg at h
    have h1 : t ^ (p ^ n) ≤ r ^ (p ^ n) := pow_le_pow_left₀ (by positivity) h _
    have h2 : r ^ (p ^ n) ≤ r ^ n :=
      pow_le_pow_of_le_one (by positivity) hr.le (Nat.lt_pow_self hp.one_lt).le
    have h3 : t ^ (p ^ n) = v (p : L) ^ p := by rw [ht, ← pow_mul, mul_comm, pow_mul, hv]
    exact absurd (lt_of_le_of_lt (h3 ▸ h1.trans h2) hn) (lt_irrefl _)
  have hs1 : s < 1 := by
    by_contra h
    push_neg at h
    have := one_le_pow₀ (n := p ^ n) h
    rw [hv] at this
    exact absurd hp1 (not_lt.mpr this)
  have ht1 : t < 1 := pow_lt_one₀ (by positivity) hs1 hp.ne_zero
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) hrt
  have hπ0 : π ≠ 0 := by
    rintro rfl
    have h0 : s = 0 := by rw [hs, map_zero]
    rw [ht, h0, zero_pow hp.ne_zero] at ht0
    exact lt_irrefl _ ht0
  have hvx : 0 < v x := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hx)
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ioc_zpow hvx ((one_lt_inv₀ ht0).mpr ht1)
  refine ⟨π ^ (m + 1), zpow_mem hπ _, zpow_ne_zero _ hπ0, ?_⟩
  have hval : v (x * (π ^ (m + 1)) ^ p) = v x * t ^ (m + 1) := by
    rw [map_mul, map_pow, map_zpow₀, ← hs, ht, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
      ← zpow_mul, mul_comm (m + 1)]
  rw [hval]
  have htne : t ≠ 0 := ht0.ne'
  constructor
  · have e : t⁻¹ ^ m * t ^ (m + 1) = t := by
      rw [inv_zpow, zpow_add_one₀ htne, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ htne), one_mul]
    calc r < t := hrt
      _ = t⁻¹ ^ m * t ^ (m + 1) := e.symm
      _ < v x * t ^ (m + 1) := mul_lt_mul_of_pos_right hm1 (zpow_pos ht0 _)
  · have e : t⁻¹ ^ (m + 1) * t ^ (m + 1) = 1 := by
      rw [inv_zpow, inv_mul_cancel₀ (zpow_ne_zero _ htne)]
    calc v x * t ^ (m + 1) ≤ t⁻¹ ^ (m + 1) * t ^ (m + 1) := mul_le_mul_of_nonneg_right hm2 (by positivity)
      _ = 1 := e

theorem klc_scale : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L,
    ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 → ∀ r : ℝ≥0, r < 1 → ∀ x : L, x ≠ 0 →
    ∃ d ∈ F, d ≠ 0 ∧ r < v (x * d ^ p) ∧ v (x * d ^ p) ≤ 1 :=
  fun L _ v p hp F hA hp0 hp1 r hr x hx => exists_scale_shell L v p hp F hA hp0 hp1 r hr x hx

end GlobalTheory.AlmostEt
