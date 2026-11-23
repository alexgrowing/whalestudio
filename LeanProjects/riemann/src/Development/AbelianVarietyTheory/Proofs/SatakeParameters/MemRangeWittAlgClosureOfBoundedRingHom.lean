import Mathlib
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist

open Filter Topology

noncomputable section

namespace GlobalTheory.TeichImage

variable {p : ℕ} [hp : Fact p.Prime]

theorem coprime_pow_sub_one {n : ℕ} (hn : 0 < n) : Nat.Coprime (p ^ n - 1) p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro h
  have h1 : p ∣ p ^ n := dvd_pow_self p hn.ne'
  have h2 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.out.pos
  have h3 : p ∣ p ^ n - (p ^ n - 1) := Nat.dvd_sub h1 h
  rw [show p ^ n - (p ^ n - 1) = 1 by omega] at h3
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 h3)

theorem mem_range_of_pow_eq {n : ℕ} (hn : 0 < n) {τ : ℂ_[p]} (hτ : τ ^ (p ^ n) = τ) :
    τ ∈ Set.range (Formalism.L2.G.Pend.wToC p) := by
  by_cases h0 : τ = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  have hq : 2 ≤ p ^ n := le_trans hp.out.two_le (Nat.le_self_pow hn.ne' p)
  have h1 : τ ^ (p ^ n - 1) = 1 := by
    have : τ ^ (p ^ n - 1) * τ = 1 * τ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hτ, one_mul]
    exact mul_right_cancel₀ h0 this
  exact Formalism.L2.G.Pend.root_mem_range p (by omega) (coprime_pow_sub_one hn) h1

theorem exists_lim {n : ℕ} (hn : 0 < n) (a : ℂ_[p])
    (ha : ∀ M : ℕ, ‖a ^ ((p ^ n) ^ (M + 1)) - a ^ ((p ^ n) ^ M)‖ ≤ ((p : ℝ)⁻¹) ^ (M + 1)) :
    ∃ τ ∈ Set.range (Formalism.L2.G.Pend.wToC p), ∀ N : ℕ, ‖a ^ ((p ^ n) ^ N) - τ‖ ≤ ((p : ℝ)⁻¹) ^ (N + 1) := by
  set r : ℝ := (p : ℝ)⁻¹ with hr
  have hr0 : 0 ≤ r := Formalism.L2.G.Pend.r_nonneg p
  have hr1 : r < 1 := Formalism.L2.G.Pend.r_lt_one p
  set u : ℕ → ℂ_[p] := fun M => a ^ ((p ^ n) ^ M) with hu
  have hcau : CauchySeq u := by
    refine cauchySeq_of_le_geometric r r hr1 fun m => ?_
    rw [dist_eq_norm, norm_sub_rev, ← pow_succ']
    exact ha m
  obtain ⟨τ, hτ⟩ := cauchySeq_tendsto_of_complete hcau
  have hball : ∀ N M : ℕ, N ≤ M → ‖u M - u N‖ ≤ r ^ (N + 1) := by
    intro N M hNM
    induction M, hNM using Nat.le_induction with
    | base => rw [sub_self, norm_zero]; exact pow_nonneg hr0 _
    | succ M hNM ih =>
      have : u (M + 1) - u N = (u (M + 1) - u M) + (u M - u N) := by ring
      rw [this]
      refine Formalism.L2.G.Pend.nadd p ((ha M).trans ?_) ih
      exact pow_le_pow_of_le_one hr0 hr1.le (by omega)
  have hlim : ∀ N : ℕ, ‖u N - τ‖ ≤ r ^ (N + 1) := by
    intro N
    have hmem : τ ∈ Metric.closedBall (u N) (r ^ (N + 1)) :=
      Metric.isClosed_closedBall.mem_of_tendsto hτ
        (eventually_atTop.2 ⟨N, fun M hM => by rw [Metric.mem_closedBall, dist_eq_norm]; exact hball N M hM⟩)
    rw [Metric.mem_closedBall, dist_eq_norm] at hmem
    rw [norm_sub_rev]; exact hmem
  have hsucc : ∀ M, u (M + 1) = u M ^ (p ^ n) := by
    intro M
    show a ^ ((p ^ n) ^ (M + 1)) = (a ^ ((p ^ n) ^ M)) ^ (p ^ n)
    rw [← pow_mul a ((p ^ n) ^ M) (p ^ n), ← pow_succ]
  have h1 : Tendsto (fun M => u (M + 1)) atTop (𝓝 τ) := hτ.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun M => u (M + 1)) atTop (𝓝 (τ ^ (p ^ n))) := by
    simp only [hsucc]; exact hτ.pow _
  have hfix : τ ^ (p ^ n) = τ := tendsto_nhds_unique h2 h1
  exact ⟨τ, mem_range_of_pow_eq hn hfix, hlim⟩

section Ring

variable {W : Type} [CommRing W] {n : ℕ}

theorem dvd_pow_iter (hW : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (N : ℕ) (x : W) :
    (p : W) ∣ x ^ ((p ^ n) ^ N) - x := by
  induction N with
  | zero => rw [pow_zero, pow_one, sub_self]; exact dvd_zero _
  | succ N ih =>
    have e : x ^ ((p ^ n) ^ (N + 1)) = (x ^ ((p ^ n) ^ N)) ^ (p ^ n) := by
      rw [← pow_mul x ((p ^ n) ^ N) (p ^ n), ← pow_succ]
    rw [e, show (x ^ ((p ^ n) ^ N)) ^ (p ^ n) - x =
      ((x ^ ((p ^ n) ^ N)) ^ (p ^ n) - x ^ ((p ^ n) ^ N)) + (x ^ ((p ^ n) ^ N) - x) by ring]
    exact dvd_add (hW _) ih

theorem dvd_pow_iter_succ (hn : 0 < n) (hW : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (M : ℕ) (x : W) :
    (p : W) ^ (M + 1) ∣ x ^ ((p ^ n) ^ (M + 1)) - x ^ ((p ^ n) ^ M) := by
  have h := dvd_sub_pow_of_dvd_sub (hW x) (n * M)
  have e1 : (x ^ (p ^ n)) ^ (p ^ (n * M)) = x ^ ((p ^ n) ^ (M + 1)) := by
    rw [← pow_mul, pow_succ, ← pow_mul, mul_comm]
  have e2 : x ^ (p ^ (n * M)) = x ^ ((p ^ n) ^ M) := by rw [← pow_mul]
  rw [e1, e2] at h
  exact (pow_dvd_pow _ (by have := Nat.le_mul_of_pos_left M hn; omega)).trans h

theorem norm_map_pow_mul (φ : W →+* ℂ_[p]) (hφ : ∀ x, ‖φ x‖ ≤ 1) (k : ℕ) (c : W) :
    ‖φ ((p : W) ^ k * c)‖ ≤ ((p : ℝ)⁻¹) ^ k := by
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Formalism.L2.G.Pend.norm_p_C]
  exact mul_le_of_le_one_right (pow_nonneg (Formalism.L2.G.Pend.r_nonneg p) k) (hφ c)

end Ring

end GlobalTheory.TeichImage

namespace GlobalTheory

theorem mem_range_wToC_of_pow_congr : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W], 0 < n →
    (∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) → IsAdicComplete (Ideal.span {(p : W)}) W →
    ∀ φ : W →+* ℂ_[p], (∀ x, ‖φ x‖ ≤ 1) → ∀ x, φ x ∈ Set.range (Formalism.L2.G.Pend.wToC p) := by
  intro p _ n W _ hn hW _ φ hφ x
  have hr0 : 0 ≤ ((p : ℝ)⁻¹) := Formalism.L2.G.Pend.r_nonneg p
  have key : ∀ k : ℕ, ∀ x : W, ∃ w, ‖φ x - Formalism.L2.G.Pend.wToC p w‖ ≤ ((p : ℝ)⁻¹) ^ k := by
    intro k
    induction k with
    | zero => intro x; exact ⟨0, by rw [map_zero, sub_zero, pow_zero]; exact hφ x⟩
    | succ k ih =>
      intro x
      obtain ⟨τ, ⟨wτ, hwτ⟩, hτ⟩ := TeichImage.exists_lim hn (φ x) (fun M => by
        obtain ⟨c, hc⟩ := TeichImage.dvd_pow_iter_succ hn hW M x
        rw [← map_pow, ← map_pow, ← map_sub, hc]
        exact TeichImage.norm_map_pow_mul φ hφ (M + 1) c)
      obtain ⟨c, hc⟩ := TeichImage.dvd_pow_iter hW k x
      obtain ⟨w₁, hw₁⟩ := ih (-c)
      refine ⟨wτ + (p : Formalism.L2.G.Pend.WW p) * w₁, ?_⟩
      have hx : x = x ^ ((p ^ n) ^ k) + (p : W) * (-c) := by linear_combination -hc
      have e : φ x - Formalism.L2.G.Pend.wToC p (wτ + (p : Formalism.L2.G.Pend.WW p) * w₁) =
          (φ x ^ ((p ^ n) ^ k) - τ) + (p : ℂ_[p]) * (φ (-c) - Formalism.L2.G.Pend.wToC p w₁) := by
        conv_lhs => rw [hx]
        rw [map_add, map_add, map_mul, map_mul, map_pow, map_natCast, map_natCast, hwτ]
        ring
      rw [e]
      refine Formalism.L2.G.Pend.nadd p ((hτ k)) ?_
      rw [norm_mul, Formalism.L2.G.Pend.norm_p_C, pow_succ']
      exact mul_le_mul_of_nonneg_left hw₁ hr0
  apply Formalism.L2.G.Pend.mem_range_of_closure p
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (Formalism.L2.G.Pend.r_lt_one p)
  obtain ⟨w, hw⟩ := key N x
  exact ⟨_, ⟨w, rfl⟩, by rw [dist_eq_norm]; exact lt_of_le_of_lt hw hN⟩

end GlobalTheory
