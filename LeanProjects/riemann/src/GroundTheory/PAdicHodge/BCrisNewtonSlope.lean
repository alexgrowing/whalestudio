import Mathlib
import GroundTheory.PAdicHodge.BCrisNewtonApprox
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WittTilt

open _root_.WittVector Laurent Filter Topology

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝔸" => Localization.Away (p : AInf K p)

theorem norm_coeffB_toB_le_one (z : 𝔸) (n : ℤ) : ‖(teichLift K p).coeffB (toB K p z) n‖ ≤ 1 := by
  obtain ⟨M, x, h⟩ := exists_toB_mul z
  rw [TeichLift.coeffB_eq _ h]
  exact norm_zcoeff_incl_le_one x _

theorem exists_gn_eq_monomial {z : 𝔸} (hz : z ≠ 0) {r₀ : ℝ} (hr0 : 0 < r₀) (hr1 : r₀ < 1) :
    ∃ (β : ℝ) (i : ℤ) (ρ₃ : ℝ), 0 < β ∧ r₀ < ρ₃ ∧ ρ₃ < 1 ∧
      ∀ ρ ∈ Set.Icc r₀ ρ₃, gn K p ρ z = β * ρ ^ i := by
  set a := (teichLift K p).coeffB (toB K p z) with ha_def
  have hconv : ∀ ρ, 0 < ρ → ρ < 1 → ConvergesAt a ρ := fun ρ h0 h1 => convergesAt_toB z h0 h1
  have ha0 : a ≠ 0 := by
    intro h
    have := gn_pos (K := K) hr0 hr1 hz
    unfold gn at this
    rw [← ha_def, h] at this
    simp [gaussNorm] at this
  set i := highIndex a r₀
  have hi := highIndex_mem hr0 (hconv r₀ hr0 hr1) ha0
  set β := ‖a i‖ with hβ_def
  have hβ : 0 < β := norm_pos_iff.2 (ne_zero_of_mem_domSet hr0 (hconv r₀ hr0 hr1) ha0 hi)
  have hG : gaussNorm a r₀ = β * r₀ ^ i := hi.symm
  set ρt := (r₀ + 1) / 2 with hρt
  have hρt0 : 0 < ρt := by linarith
  have hρt1 : ρt < 1 := by linarith
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one hβ hρt1
  have hev : ∀ᶠ ρ in 𝓝 r₀, ∀ n ∈ Finset.Ioc i (i + L), ‖a n‖ * ρ ^ n < β * ρ ^ i := by
    rw [Filter.eventually_all_finset]
    intro n hn
    have hlt : ‖a n‖ * r₀ ^ n < β * r₀ ^ i := by
      rw [← hG]
      exact weight_lt_of_highIndex_lt hr0 (hconv r₀ hr0 hr1) ha0 (Finset.mem_Ioc.1 hn).1
    have hc : ContinuousAt (fun ρ : ℝ => β * ρ ^ i - ‖a n‖ * ρ ^ n) r₀ :=
      (continuousAt_const.mul (continuousAt_zpow₀ r₀ i (Or.inl hr0.ne'))).sub
        (continuousAt_const.mul (continuousAt_zpow₀ r₀ n (Or.inl hr0.ne')))
    filter_upwards [hc.eventually (lt_mem_nhds (sub_pos.2 hlt))] with ρ hρ
    exact sub_pos.1 hρ
  obtain ⟨δ, hδ, hδf⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨β, i, min (r₀ + δ / 2) ρt, hβ, lt_min (by linarith) (by linarith),
    (min_le_right _ _).trans_lt hρt1, fun ρ hρ => ?_⟩
  have hρ0 : 0 < ρ := hr0.trans_le hρ.1
  have hρ1 : ρ < 1 := hρ.2.trans_lt ((min_le_right _ _).trans_lt hρt1)
  have hρt' : ρ ≤ ρt := hρ.2.trans (min_le_right _ _)
  have hd : dist ρ r₀ < δ := by
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hρ.1])]
    linarith [hρ.2, min_le_left (r₀ + δ / 2) ρt]
  have hnear := hδf hd
  unfold gn
  rw [← ha_def]
  refine le_antisymm (gaussNorm_le fun n => ?_) ((hconv ρ hρ0 hρ1).le_gaussNorm i)
  rcases le_or_gt n i with hni | hni
  ·
    have h1 : ‖a n‖ * r₀ ^ n ≤ β * r₀ ^ i := hG ▸ (hconv r₀ hr0 hr1).le_gaussNorm n
    have hq : 1 ≤ ρ / r₀ := (one_le_div hr0).2 hρ.1
    have h2 : (ρ / r₀) ^ n ≤ (ρ / r₀) ^ i := zpow_le_zpow_right₀ hq hni
    have e1 : ‖a n‖ * ρ ^ n = (‖a n‖ * r₀ ^ n) * (ρ / r₀) ^ n := by
      rw [div_zpow, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (zpow_ne_zero n hr0.ne')]
    have e2 : β * ρ ^ i = (β * r₀ ^ i) * (ρ / r₀) ^ i := by
      rw [div_zpow, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (zpow_ne_zero i hr0.ne')]
    rw [e1, e2]
    exact mul_le_mul h1 h2 (zpow_nonneg (div_nonneg hρ0.le hr0.le) n)
      (mul_nonneg hβ.le (zpow_nonneg hr0.le i))
  · rcases le_or_gt n (i + L) with hnL | hnL
    · exact (hnear n (Finset.mem_Ioc.2 ⟨hni, hnL⟩)).le
    ·
      have h1 : ‖a n‖ * ρ ^ n ≤ ρ ^ n :=
        mul_le_of_le_one_left (zpow_nonneg hρ0.le n) (norm_coeffB_toB_le_one z n)
      have h2 : ρ ^ n = ρ ^ i * ρ ^ (n - i) := by rw [← zpow_add₀ hρ0.ne']; ring_nf
      have h3 : ρ ^ (n - i) ≤ ρ ^ (L : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ hρ0 hρ1.le (by omega)
      have h4 : ρ ^ (L : ℤ) ≤ ρt ^ L := by
        rw [zpow_natCast]; exact pow_le_pow_left₀ hρ0.le hρt' L
      have h5 : ρ ^ (n - i) ≤ β := (h3.trans h4).trans hL.le
      calc ‖a n‖ * ρ ^ n ≤ ρ ^ i * ρ ^ (n - i) := h1.trans h2.le
        _ ≤ ρ ^ i * β := mul_le_mul_of_nonneg_left h5 (zpow_nonneg hρ0.le i)
        _ = β * ρ ^ i := mul_comm _ _

end WittTilt

end GroundTheory.PAdicHodge
