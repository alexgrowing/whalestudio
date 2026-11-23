import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthUpperHalfLog
open GlobalTheory.ShFam.Hor
open scoped Topology

namespace GlobalTheory.UpperGrowth

open Complex

theorem qf_le_base (n a : ℕ) (F : (Fin n → ℂ) → ℂ) (hF : DifferentiableOn ℂ F (logDom n a))
    (hpos : ∀ s ∈ logDom n a, 0 < (F s).im) (s : Fin n → ℂ) (hs : s ∈ logDom n a)
    (hse : ‖logExp a s‖ ≤ 1 / 2) :
    qf (F s) ≤ 64 ^ n * (1 + ‖s‖) ^ (6 * n) * qf (F (fun k => if (k : ℕ) < a then -1 else 0)) := by
  set s₀ : Fin n → ℂ := fun k => if (k : ℕ) < a then -1 else 0 with hs₀
  set P : ℕ → Fin n → ℂ := fun j k => if (k : ℕ) < j then s k else s₀ k with hP
  have hs' : ∀ k : Fin n, if (k : ℕ) < a then (s k).re < 0 else ‖s k‖ < 1 := by
    simpa [logDom] using hs
  have hs₀' : ∀ k : Fin n, if (k : ℕ) < a then (s₀ k).re < 0 else ‖s₀ k‖ < 1 := by
    intro k; simp only [hs₀]; split_ifs <;> norm_num
  have hPmem : ∀ j, P j ∈ logDom n a := by
    intro j
    simp only [logDom, Set.mem_setOf_eq]
    intro k
    by_cases hk : (k : ℕ) < j
    · have e : P j k = s k := if_pos hk
      rw [e]; exact hs' k
    · have e : P j k = s₀ k := if_neg hk
      rw [e]; exact hs₀' k
  have hco : ∀ k : Fin n, ‖logExp a s k‖ ≤ 1 / 2 := fun k => (norm_le_pi_norm (logExp a s) k).trans hse
  have hsk : ∀ k : Fin n, ‖s k‖ ≤ ‖s‖ := fun k => norm_le_pi_norm s k
  set M : ℝ := 4 * (1 + ‖s‖) ^ 2 with hMdef
  have hM1 : 1 ≤ M := by
    have : 1 ≤ (1 + ‖s‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg s])
    linarith
  have step : ∀ j, qf (F (P (j + 1))) ≤ M ^ 3 * qf (F (P j)) := by
    intro j
    by_cases hj : j < n
    · set i : Fin n := ⟨j, hj⟩ with hi
      have hPi : P (j + 1) = Function.update (P j) i (s i) := by
        funext k
        by_cases hk : k = i
        · rw [hk, Function.update_self]
          exact if_pos (show (i : ℕ) < j + 1 by simp [hi])
        · rw [Function.update_of_ne hk]
          have hkj : (k : ℕ) ≠ j := fun h => hk (Fin.ext h)
          have e : ((k : ℕ) < j + 1 ↔ (k : ℕ) < j) := by omega
          simp only [hP, e]
      have hPj : Function.update (P j) i (s₀ i) = P j := by
        rw [Function.update_eq_self_iff]
        have hn : ¬ ((i : ℕ) < j) := by simp [hi]
        exact (if_neg hn).symm
      by_cases ha : j < a
      · have hai : (i : ℕ) < a := ha
        have hre : (s i).re ≤ -1 / 2 := by
          apply re_le_of_exp
          have := hco i
          simpa [logExp, hai] using this
        obtain ⟨hζ, hMb⟩ := cay_bound hre
        have hdf : DifferentiableOn ℂ (fun ζ => F (Function.update (P j) i (cay ζ))) (Metric.ball 0 1) :=
          (upd_diff hF (hPmem j) i (D := {z | z.re < 0}) (fun z hz => by simpa [hai] using hz)).comp
            cay_diff (fun ζ hζ => cay_re hζ)
        have hposf : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < (F (Function.update (P j) i (cay z))).im :=
          fun z hz => hpos _ (upd_mem (hPmem j) i (by simpa [hai] using cay_re hz))
        have key := qf_ball_le hdf hposf hζ (M := M)
          (hMb.trans (by rw [hMdef]; gcongr; exact hsk i))
        have hsi : (s i).re < 0 := by simpa [hai] using hs' i
        have e0 : s₀ i = -1 := by simp [hs₀, hai]
        simp only [cay_inv hsi, cay_zero] at key
        rw [← e0, hPj] at key
        rw [hPi]
        exact key
      · have hai : ¬ (i : ℕ) < a := ha
        have hle : ‖s i‖ ≤ 1 / 2 := by
          have := hco i
          simpa [logExp, hai] using this
        have hζ : ‖s i‖ < 1 := by linarith
        have hdf : DifferentiableOn ℂ (fun ζ => F (Function.update (P j) i ζ)) (Metric.ball 0 1) :=
          upd_diff hF (hPmem j) i (fun z hz => by simpa [hai] using hz)
        have hposf : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < (F (Function.update (P j) i z)).im :=
          fun z hz => hpos _ (upd_mem (hPmem j) i (by simpa [hai] using hz))
        have hMb : 2 / (1 - ‖s i‖) ≤ M := by
          rw [div_le_iff₀ (by linarith)]
          have : 1 ≤ (1 + ‖s‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg s])
          nlinarith
        have key := qf_ball_le hdf hposf hζ hMb
        have e0 : s₀ i = 0 := by simp [hs₀, hai]
        rw [← e0, hPj, ← hPi] at key
        exact key
    · have e : P (j + 1) = P j := by
        funext k
        have e : ((k : ℕ) < j + 1 ↔ (k : ℕ) < j) := by have := k.isLt; omega
        simp only [hP, e]
      rw [e]
      have h0 := qf_nonneg (hpos _ (hPmem j))
      have : 1 ≤ M ^ 3 := one_le_pow₀ hM1
      nlinarith
  have hind : ∀ j, qf (F (P j)) ≤ (M ^ 3) ^ j * qf (F s₀) := by
    intro j
    induction j with
    | zero =>
      have e : P 0 = s₀ := by funext k; simp [hP]
      simp [e]
    | succ j ih =>
      have : 0 ≤ M ^ 3 := by positivity
      calc qf (F (P (j + 1))) ≤ M ^ 3 * qf (F (P j)) := step j
        _ ≤ M ^ 3 * ((M ^ 3) ^ j * qf (F s₀)) := mul_le_mul_of_nonneg_left ih this
        _ = (M ^ 3) ^ (j + 1) * qf (F s₀) := by ring
  have hPn : P n = s := by funext k; simp [hP, k.isLt]
  have hfin := hind n
  rw [hPn] at hfin
  refine hfin.trans (le_of_eq ?_)
  have e : M ^ 3 = 64 * (1 + ‖s‖) ^ 6 := by rw [hMdef]; ring
  rw [e, mul_pow, pow_mul]

theorem inv_im_le_qf {w : ℂ} (hw : 0 < w.im) : 1 / w.im ≤ qf w := by
  unfold qf
  exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg ‖w‖]) hw.le

end GlobalTheory.UpperGrowth

namespace GlobalTheory.UpperGrowth

open Complex

theorem qsum_smul {d : ℕ} (A : Fin d → Fin d → ℂ) (t : ℝ) (u : Fin d → ℝ) :
    (∑ i, ∑ j, (((t • u) i : ℝ) : ℂ) * A i j * (((t • u) j : ℝ) : ℂ)) =
      ((t ^ 2 : ℝ) : ℂ) * ∑ i, ∑ j, (u i : ℂ) * A i j * (u j : ℂ) := by
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

theorem qsum_norm_le {d : ℕ} (A : Fin d → Fin d → ℂ) (u : Fin d → ℝ) (hu : ‖u‖ ≤ 1) :
    ‖∑ i, ∑ j, (u i : ℂ) * A i j * (u j : ℂ)‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j _ => ?_))
  have hi : ‖(u i : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real]; exact (norm_le_pi_norm u i).trans hu
  have hj : ‖(u j : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real]; exact (norm_le_pi_norm u j).trans hu
  rw [norm_mul, norm_mul]
  calc ‖(u i : ℂ)‖ * ‖A i j‖ * ‖(u j : ℂ)‖ ≤ 1 * ‖A i j‖ * 1 := by gcongr
    _ = ‖A i j‖ := by ring

theorem qsum_cont {d : ℕ} (A : Fin d → Fin d → ℂ) :
    Continuous (fun v : Fin d → ℝ => (∑ i, ∑ j, (v i : ℂ) * A i j * (v j : ℂ)).im) := by
  fun_prop

theorem qsum_diff {n d : ℕ} {D : Set (Fin n → ℂ)} (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ)
    (hτ : DifferentiableOn ℂ τ D) (v : Fin d → ℝ) :
    DifferentiableOn ℂ (fun s => ∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)) D := by
  have hτij : ∀ i j, DifferentiableOn ℂ (fun s => τ s i j) D :=
    fun i j => differentiableOn_pi.mp (differentiableOn_pi.mp hτ i) j
  fun_prop

end GlobalTheory.UpperGrowth

namespace GlobalTheory

open GlobalTheory.UpperGrowth in

theorem period_im_lower_bound : ∀ (n a d : ℕ) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ),
    DifferentiableOn ℂ τ (logDom n a) →
    (∀ s ∈ logDom n a, ∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)).im) →
    ∃ (c : ℝ) (k : ℕ), 0 < c ∧ ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → ∀ v : Fin d → ℝ,
      c * ‖v‖ ^ 2 ≤ (1 + ‖s‖) ^ k * (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)).im := by
  intro n a d τ hτ hpd
  set s₀ : Fin n → ℂ := fun k => if (k : ℕ) < a then -1 else 0 with hs₀
  have hs₀mem : s₀ ∈ logDom n a := by
    simp only [logDom, Set.mem_setOf_eq, hs₀]
    intro k; split_ifs <;> norm_num

  have hunit : ∀ v : Fin d → ℝ, v ≠ 0 → ‖(‖v‖⁻¹ • v)‖ = 1 ∧ v = ‖v‖ • (‖v‖⁻¹ • v) := by
    intro v hv
    have ht : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    refine ⟨?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ht]
    · rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
  have hzero : ∀ s : Fin n → ℂ, ∀ (c : ℝ) (k : ℕ),
      c * ‖(0 : Fin d → ℝ)‖ ^ 2 ≤ (1 + ‖s‖) ^ k *
        (∑ i, ∑ j, (((0 : Fin d → ℝ) i : ℝ) : ℂ) * τ s i j * (((0 : Fin d → ℝ) j : ℝ) : ℂ)).im := by
    intro s c k; simp
  by_cases hS : (Metric.sphere (0 : Fin d → ℝ) 1).Nonempty
  swap
  · refine ⟨1, 0, one_pos, fun s _ _ v => ?_⟩
    by_cases hv : v = 0
    · subst hv; exact hzero s 1 0
    · exact absurd ⟨_, mem_sphere_zero_iff_norm.mpr (hunit v hv).1⟩ hS
  obtain ⟨u₀, hu₀, hmin⟩ := (isCompact_sphere (0 : Fin d → ℝ) 1).exists_isMinOn hS
    (qsum_cont (τ s₀)).continuousOn
  set m₀ := (∑ i, ∑ j, (u₀ i : ℂ) * τ s₀ i j * (u₀ j : ℂ)).im with hm₀
  have hu₀n : ‖u₀‖ = 1 := mem_sphere_zero_iff_norm.mp hu₀
  have hu₀ne : u₀ ≠ 0 := by intro h; rw [h, norm_zero] at hu₀n; exact zero_ne_one hu₀n
  have hm₀pos : 0 < m₀ := hpd s₀ hs₀mem u₀ hu₀ne
  set B := ∑ i, ∑ j, ‖τ s₀ i j‖ with hB
  set K := (1 + B ^ 2) / m₀ with hK
  have hKpos : 0 < K := by positivity
  have hL0 : (0 : ℝ) < 64 ^ n * K := by positivity
  refine ⟨1 / (64 ^ n * K), 6 * n, by positivity, fun s hs hse v => ?_⟩
  by_cases hv : v = 0
  · subst hv; exact hzero s _ _
  obtain ⟨hun, hvu⟩ := hunit v hv
  set u := ‖v‖⁻¹ • v with hudef
  have hune : u ≠ 0 := by intro h; rw [h, norm_zero] at hun; exact zero_ne_one hun
  set Fu : (Fin n → ℂ) → ℂ := fun s => ∑ i, ∑ j, (u i : ℂ) * τ s i j * (u j : ℂ) with hFu
  have hFupos : ∀ s ∈ logDom n a, 0 < (Fu s).im := fun s hs => hpd s hs u hune
  have h1 := qf_le_base n a Fu (qsum_diff τ hτ u) hFupos s hs hse
  have h2 : qf (Fu s₀) ≤ K := by
    have hw := hFupos s₀ hs₀mem
    have hmle : m₀ ≤ (Fu s₀).im := hmin (mem_sphere_zero_iff_norm.mpr hun)
    have hnB : ‖Fu s₀‖ ≤ B := qsum_norm_le (τ s₀) u hun.le
    unfold qf
    rw [hK, div_le_div_iff₀ hw hm₀pos]
    have : ‖Fu s₀‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnB 2
    nlinarith [sq_nonneg B]
  have h3 := inv_im_le_qf (hFupos s hs)
  set x := (Fu s).im with hx
  have hxpos : 0 < x := hFupos s hs
  set P := (1 + ‖s‖) ^ (6 * n) with hP
  have hPpos : 0 < P := by positivity
  have h4 : 1 / x ≤ 64 ^ n * K * P := by
    have hq := qf_nonneg (hFupos s₀ hs₀mem)
    calc 1 / x ≤ qf (Fu s) := h3
      _ ≤ 64 ^ n * P * qf (Fu s₀) := h1
      _ ≤ 64 ^ n * P * K := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 64 ^ n * K * P := by ring
  have h5 : 1 / (64 ^ n * K) ≤ P * x := by
    rw [div_le_iff₀ hxpos] at h4
    rw [div_le_iff₀ hL0]
    nlinarith
  have hsum : (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)) = ((‖v‖ ^ 2 : ℝ) : ℂ) * Fu s := by
    have := qsum_smul (τ s) ‖v‖ u
    rw [← hvu] at this
    exact this
  rw [hsum, Complex.im_ofReal_mul, ← hx]
  have ht : 0 ≤ ‖v‖ ^ 2 := by positivity
  calc 1 / (64 ^ n * K) * ‖v‖ ^ 2 ≤ P * x * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right h5 ht
    _ = P * (‖v‖ ^ 2 * x) := by ring

end GlobalTheory
