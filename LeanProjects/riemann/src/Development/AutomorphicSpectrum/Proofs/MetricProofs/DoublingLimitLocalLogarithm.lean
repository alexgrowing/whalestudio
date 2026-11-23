import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IterDifferentiableOn
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalLog

theorem koenigs_step {B V : Type} [NormedAddCommGroup B] [NormedAddCommGroup V]
    [NormedSpace ℂ V] (b₀ : B) (h : B × V → V) (ρ C : ℝ) (hC : 0 ≤ C)
    (hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖)
    (hquad : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2)
    {b : B} (hb : b ∈ ball b₀ ρ) {s : V} (hs : s ∈ ball (0 : V) ρ) (k : ℕ) :
    dist ((2 : ℂ) ^ k • iter h k (b, s)) ((2 : ℂ) ^ (k + 1) • iter h (k + 1) (b, s))
      ≤ C * ‖s‖ ^ 2 * (18 / 25) ^ k := by
  rw [dist_eq_norm, iter_succ, pow_succ, mul_smul, ← smul_sub, norm_smul, norm_sub_rev]
  have hx := iter_mem_ball b₀ h ρ hcontr hb hs k
  have hxn := norm_iter_le b₀ h ρ hcontr hb hs k
  have h2 : ‖(2 : ℂ) ^ k‖ = (2 : ℝ) ^ k := by simp
  rw [h2]
  calc (2 : ℝ) ^ k * ‖(2 : ℂ) • h (b, iter h k (b, s)) - iter h k (b, s)‖
      ≤ (2 : ℝ) ^ k * (C * ‖iter h k (b, s)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hquad b hb _ hx) (by positivity)
    _ ≤ (2 : ℝ) ^ k * (C * ((3 / 5) ^ k * ‖s‖) ^ 2) := by gcongr
    _ = C * ‖s‖ ^ 2 * (18 / 25) ^ k := by
        have e : (18 / 25 : ℝ) ^ k = 2 ^ k * ((3 / 5) ^ k) ^ 2 := by
          rw [← pow_mul, mul_comm k 2, pow_mul, ← mul_pow]
          norm_num
        rw [e]
        ring

theorem koenigs_limit : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b₀ : B) (h : B × V → V)
    (ρ C : ℝ), 0 < ρ → 0 ≤ C →
    (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) →
    (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2) →
    ∃ L : B × V → V,
      TendstoUniformlyOn (fun (k : ℕ) (p : B × V) => (2 : ℂ) ^ k • iter h k p) L atTop
        (ball b₀ ρ ×ˢ ball (0 : V) ρ) ∧
      ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖L (b, s) - s‖ ≤ 4 * C * ‖s‖ ^ 2 := by
  intro B V _ _ _ _ _ b₀ h ρ C hρ hC hcontr hquad
  set F : ℕ → B × V → V := fun k p => (2 : ℂ) ^ k • iter h k p with hF
  have hstep : ∀ p ∈ ball b₀ ρ ×ˢ ball (0 : V) ρ, ∀ k : ℕ,
      dist (F k p) (F (k + 1) p) ≤ C * ‖p.2‖ ^ 2 * (18 / 25) ^ k := by
    rintro ⟨b, s⟩ ⟨hb, hs⟩ k
    exact koenigs_step b₀ h ρ C hC hcontr hquad hb hs k
  have hr : (18 / 25 : ℝ) < 1 := by norm_num
  have hcauchy : ∀ p ∈ ball b₀ ρ ×ˢ ball (0 : V) ρ, CauchySeq (fun k => F k p) :=
    fun p hp => cauchySeq_of_le_geometric _ _ hr (hstep p hp)
  let L : B × V → V := fun p => limUnder atTop (fun k => F k p)
  have hlim : ∀ p ∈ ball b₀ ρ ×ˢ ball (0 : V) ρ, Tendsto (fun k => F k p) atTop (𝓝 (L p)) :=
    fun p hp => (hcauchy p hp).tendsto_limUnder
  have hdist : ∀ p ∈ ball b₀ ρ ×ˢ ball (0 : V) ρ, ∀ n : ℕ,
      dist (F n p) (L p) ≤ C * ‖p.2‖ ^ 2 * (18 / 25) ^ n / (7 / 25) := by
    intro p hp n
    have h1 := dist_le_of_le_geometric_of_tendsto _ _ hr (hstep p hp) (hlim p hp) n
    rwa [show (1 - 18 / 25 : ℝ) = 7 / 25 by norm_num] at h1
  refine ⟨L, ?_, ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hg : Tendsto (fun n : ℕ => C * ρ ^ 2 * (18 / 25 : ℝ) ^ n / (7 / 25)) atTop (𝓝 0) := by
      have h1 := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 18 / 25) hr).const_mul
        (C * ρ ^ 2)).div_const (7 / 25 : ℝ)
      simpa using h1
    filter_upwards [hg.eventually (gt_mem_nhds hε)] with n hn
    rintro ⟨b, s⟩ hp
    rw [dist_comm]
    refine lt_of_le_of_lt ((hdist _ hp n).trans ?_) hn
    have hs : ‖s‖ < ρ := by simpa using hp.2
    have hsle : ‖s‖ ≤ ρ := hs.le
    have hsq : ‖s‖ ^ 2 ≤ ρ ^ 2 := by gcongr
    show C * ‖s‖ ^ 2 * (18 / 25) ^ n / (7 / 25) ≤ C * ρ ^ 2 * (18 / 25) ^ n / (7 / 25)
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hsq hC
  · intro b hb s hs
    have h0 := hdist (b, s) ⟨hb, hs⟩ 0
    have e0 : F 0 (b, s) = s := by simp [hF]
    rw [e0, dist_comm, dist_eq_norm] at h0
    calc ‖L (b, s) - s‖ ≤ C * ‖s‖ ^ 2 * (18 / 25) ^ 0 / (7 / 25) := h0
      _ ≤ 4 * C * ‖s‖ ^ 2 := by
        rw [pow_zero, mul_one, div_le_iff₀ (by norm_num)]
        nlinarith [mul_nonneg hC (sq_nonneg ‖s‖)]

end GlobalTheory.CompanionTheory.Ar.Flat.LocalLog
