import Mathlib
import GroundTheory.PAdicHodge.WABridgeGerm
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WABridge

open _root_.WittVector WittTilt WAEval TeichLift PhiGamma Laurent

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)

theorem lt_rootRadius (τ : Set.Ioo (0 : ℝ) 1) : (τ : ℝ) < (frob ℂ_[p] p).rootRadius τ := by
  rw [rootRadius_coe]
  have h := Real.rpow_lt_rpow_of_exponent_gt τ.2.1 τ.2.2 (inv_p_lt_one (p := p))
  rwa [Real.rpow_one] at h

variable (p) in

def radTwo : Set.Ioo (0 : ℝ) 1 := (frob ℂ_[p] p).rootRadius (rhoMid p)

variable (p) in

def radC : Set.Ioo (0 : ℝ) 1 := (frob ℂ_[p] p).rootRadius (radTwo p)

theorem inv_p_lt_radTwo : (p : ℝ)⁻¹ < radTwo p :=
  inv_p_lt_rhoMid.trans_le (le_rootRadius (rhoMid p))

theorem radA_lt_inv_p : radA p < (p : ℝ)⁻¹ := by
  have h := pow_lt_pow_right_of_lt_one₀ (inv_p_pos (p := p)) inv_p_lt_one hp.out.one_lt
  rw [pow_one] at h
  exact h

theorem radA_lt_radTwo : radA p < radTwo p := radA_lt_inv_p.trans inv_p_lt_radTwo

theorem radTwo_lt_radC : (radTwo p : ℝ) < radC p := lt_rootRadius (radTwo p)

theorem radC_le_iterate (k : ℕ) :
    (radC p : ℝ) ≤ ((frob ℂ_[p] p).rootRadius^[k] (radC p) : Set.Ioo (0 : ℝ) 1) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.trans (le_rootRadius _)

theorem pow_iterate_rootRadius (c : Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    (((frob ℂ_[p] p).rootRadius^[k] c : Set.Ioo (0 : ℝ) 1) : ℝ) ^ (p ^ k) = c := by
  rw [← coe_iterate_powRadius, iterate_powRadius_rootRadius]

theorem exists_approx {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) {M : ℝ} (hM : 1 ≤ M)
    (hdec : ∀ k : ℕ, tn hx ((frob ℂ_[p] p).rootRadius^[k] (radC p)) ^ (p ^ k) ≤
      (radC p : ℝ) ^ k * M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : 𝔸, (∀ r : Set.Ioc (0 : ℝ) (radTwo p), radA p ≤ r →
        (𝓣).extNorm (radTwo p) r (rep hx (radTwo p) - awayToExt p (radTwo p) s) ≤ ε) ∧
      gn ℂ_[p] p (radA p) s ≤ max (tn hx ⟨radA p, radA_pos, radA_lt_one⟩) 1 := by
  set c : ℝ := ((radC p : Set.Ioo (0 : ℝ) 1) : ℝ) with hc
  have hc0 : 0 < c := (radC p).2.1
  have hc1 : c < 1 := (radC p).2.2
  set q : ℝ := ((radTwo p : Set.Ioo (0 : ℝ) 1) : ℝ) / c with hq
  have hq0 : 0 < q := div_pos (radTwo p).2.1 hc0
  have hq1 : q < 1 := (div_lt_one hc0).2 radTwo_lt_radC
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hM0) hc1
  obtain ⟨k₂, hk₂⟩ := exists_pow_lt_of_lt_one (mul_pos hε (pow_pos hq0 L)) hq1
  set k := max L k₂ with hk
  set b : Set.Ioo (0 : ℝ) 1 := (frob ℂ_[p] p).rootRadius^[k] (radC p) with hb
  have hb0 : (0 : ℝ) < b := b.2.1
  have hb1 : (b : ℝ) < 1 := b.2.2
  have hcb : c ≤ b := radC_le_iterate k
  have hbk : (b : ℝ) ^ (p ^ k) = c := pow_iterate_rootRadius _ k
  have hckM : c ^ k * M < 1 := by
    have h1 : c ^ k ≤ c ^ L := pow_le_pow_of_le_one hc0.le hc1.le (le_max_left _ _)
    have h2 : c ^ k < M⁻¹ := h1.trans_lt hL
    calc c ^ k * M < M⁻¹ * M := mul_lt_mul_of_pos_right h2 hM0
      _ = 1 := inv_mul_cancel₀ hM0.ne'
  have hck1 : c ^ k ≤ 1 := pow_le_one₀ hc0.le hc1.le
  set δ : ℝ := min ε (c ^ k) with hδ
  have hδ0 : 0 < δ := lt_min hε (pow_pos hc0 k)
  have hradA_b : radA p ≤ b :=
    (radA_lt_radTwo.trans radTwo_lt_radC).le.trans hcb
  obtain ⟨d, hd, hdapp⟩ := (𝓣).exists_approx_convAll (rep hx b) ⟨radA p, radA_pos, hradA_b⟩ hδ0
  have hdb : ConvergesAt ((𝓣).coeffB d) b := hd b hb0 hb1
  set β : ℝ := gaussNorm ((𝓣).coeffB d) b with hβdef
  have hβ0 : 0 ≤ β := gaussNorm_nonneg hb0
  have hβ : β ≤ max (tn hx b) δ := by
    have e1 : β = (𝓣).extNorm b (topRad b) ((𝓣).ofAll d hd b) := ((𝓣).extNorm_ofAll hd (topRad b)).symm
    have e2 : (𝓣).ofAll d hd b = rep hx b + -(rep hx b - (𝓣).ofAll d hd b) := by ring
    rw [e1, e2]
    refine ((𝓣).extNorm_add_le _ _ _).trans (max_le_max le_rfl ?_)
    rw [(𝓣).extNorm_neg]
    exact hdapp (topRad b) hradA_b
  have hβk : β ^ (p ^ k) ≤ c ^ k * M := by
    have hpk : p ^ k ≠ 0 := pow_ne_zero _ hp.out.ne_zero
    refine (pow_le_pow_left₀ hβ0 hβ _).trans ?_
    rcases le_total (tn hx b) δ with h | h
    · rw [max_eq_right h]
      calc δ ^ (p ^ k) ≤ (c ^ k) ^ (p ^ k) := pow_le_pow_left₀ hδ0.le (min_le_right _ _) _
        _ ≤ c ^ k := pow_le_of_le_one (pow_nonneg hc0.le _) hck1 hpk
        _ ≤ c ^ k * M := le_mul_of_one_le_right (pow_nonneg hc0.le _) hM
    · rw [max_eq_left h]
      exact hdec k
  have hβ1 : β < 1 := by
    by_contra hcon
    have := one_le_pow₀ (n := p ^ k) (not_lt.1 hcon)
    linarith

  set S := (𝓣).smallPart 1 d with hSdef
  set G := (𝓣).bigPart 1 d with hGdef
  have hSG : S + G = d := (𝓣).smallPart_add_bigPart 1 d
  have hS : (𝓣).ConvAll S := fun ρ h0 h1 =>
    (convergesAt_of_norm_le h0 ((𝓣).norm_coeffB_smallPart_le zero_lt_one d) (hd ρ h0 h1)).1
  have hG : (𝓣).ConvAll G := fun ρ h0 h1 =>
    (convergesAt_of_norm_le h0 ((𝓣).norm_coeffB_bigPart_le 1 d) (hd ρ h0 h1)).1

  have hGdig : ∀ n : ℤ, (𝓣).coeffB G n ≠ 0 →
      ‖(𝓣).coeffB G n‖ * (b : ℝ) ^ n ≤ β ∧ 0 ≤ n ∧ (k : ℤ) - L ≤ n := by
    intro n hn
    have h1 : 1 ≤ ‖(𝓣).coeffB G n‖ := ((𝓣).coeffB_bigPart_eq_zero_or 1 d n).resolve_left hn
    have e : (𝓣).coeffB G n = (𝓣).coeffB d n := by
      rw [hGdef, (𝓣).coeffB_bigPart]
      split_ifs with h
      · exact absurd (by rw [hGdef, (𝓣).coeffB_bigPart, if_pos h]) hn
      · rfl
    have h2 : ‖(𝓣).coeffB G n‖ * (b : ℝ) ^ n ≤ β := by rw [e]; exact hdb.le_gaussNorm n
    have h3 : (b : ℝ) ^ n ≤ β :=
      (le_mul_of_one_le_left (zpow_nonneg hb0.le n) h1).trans h2
    refine ⟨h2, ?_, ?_⟩
    · by_contra hneg
      have := one_le_zpow_of_nonpos₀ hb0 hb1.le (not_le.1 hneg).le
      linarith
    · have h4 : ((b : ℝ) ^ n) ^ (p ^ k) ≤ c ^ k * M :=
        (pow_le_pow_left₀ (zpow_nonneg hb0.le n) h3 _).trans hβk
      have h5 : ((b : ℝ) ^ n) ^ (p ^ k) = c ^ n := by
        rw [← hbk, ← zpow_natCast, ← zpow_natCast ((b : ℝ)) (p ^ k), ← zpow_mul, ← zpow_mul,
          mul_comm]
      have h6 : M ≤ (c ^ L)⁻¹ := by
        rw [le_inv_comm₀ hM0 (pow_pos hc0 L)]; exact hL.le
      have h7 : c ^ n ≤ c ^ ((k : ℤ) - L) := by
        rw [zpow_sub₀ hc0.ne', zpow_natCast, zpow_natCast, div_eq_mul_inv]
        rw [← h5]
        exact h4.trans (mul_le_mul_of_nonneg_left h6 (pow_nonneg hc0.le _))
      exact (zpow_le_zpow_iff_right_of_lt_one₀ hc0 hc1).1 h7
  have hGnorm : ∀ r : ℝ, 0 < r → r ≤ radTwo p → gaussNorm ((𝓣).coeffB G) r ≤ ε := by
    intro r hr0 hr
    refine gaussNorm_le fun n => ?_
    by_cases hn : (𝓣).coeffB G n = 0
    · rw [hn, norm_zero, zero_mul]; exact hε.le
    obtain ⟨h2, hn0, hnk⟩ := hGdig n hn
    have hrb : r / b ≤ q := by
      rw [hq]
      exact div_le_div₀ (radTwo p).2.1.le hr hc0 hcb
    have e : ‖(𝓣).coeffB G n‖ * r ^ n = (‖(𝓣).coeffB G n‖ * (b : ℝ) ^ n) * (r / b) ^ n := by
      rw [div_zpow, mul_assoc, mul_div_cancel₀ _ (zpow_ne_zero _ hb0.ne')]
    rw [e]
    calc (‖(𝓣).coeffB G n‖ * (b : ℝ) ^ n) * (r / b) ^ n ≤ 1 * q ^ n :=
          mul_le_mul (h2.trans hβ1.le) (zpow_le_zpow_left₀ hn0 (div_nonneg hr0.le hb0.le) hrb)
            (zpow_nonneg (div_nonneg hr0.le hb0.le) _) zero_le_one
      _ = q ^ n := one_mul _
      _ ≤ q ^ ((k : ℤ) - L) := zpow_le_zpow_right_of_le_one₀ hq0 hq1.le hnk
      _ ≤ ε := by
        rw [zpow_sub₀ hq0.ne', zpow_natCast, zpow_natCast, div_le_iff₀ (pow_pos hq0 L)]
        exact ((pow_le_pow_of_le_one hq0.le hq1.le (le_max_right _ _)).trans hk₂.le)

  have hSdig : ∀ n, ‖(𝓣).coeffB S n‖ ≤ 1 := fun n =>
    ((𝓣).norm_coeffB_smallPart_lt zero_lt_one d n).le
  obtain ⟨s, hs⟩ := exists_toB_eq_of_norm_coeffB_le_one hSdig
  have hSd : (𝓣).ofAll d hd b = (𝓣).ofAll S hS b + (𝓣).ofAll G hG b := by
    rw [← (𝓣).ofAll_add hS hG]; exact (𝓣).ofAll_congr _ _ hSG.symm b
  have hb2 : (radTwo p : ℝ) ≤ b := radTwo_lt_radC.le.trans hcb
  refine ⟨s, fun r hr => ?_, ?_⟩
  · have e1 : rep hx (radTwo p) - awayToExt p (radTwo p) s =
        (𝓣).res hb2 (rep hx b - (𝓣).ofAll S hS b) := by
      rw [map_sub, res_rep, (𝓣).res_ofAll, awayToExt_eq_ofAll]
      congr 1
      exact (𝓣).ofAll_congr _ _ hs _
    rw [e1, (𝓣).extNorm_res]
    have e2 : rep hx b - (𝓣).ofAll S hS b = (rep hx b - (𝓣).ofAll d hd b) + (𝓣).ofAll G hG b := by
      rw [hSd]; ring
    rw [e2]
    refine ((𝓣).extNorm_add_le _ _ _).trans (max_le ?_ ?_)
    · exact (hdapp _ hr).trans (min_le_left _ _)
    · rw [(𝓣).extNorm_ofAll]
      exact hGnorm r r.2.1 r.2.2
  · have hradA : (0 : ℝ) < radA p := radA_pos
    have e1 : gn ℂ_[p] p (radA p) s = gaussNorm ((𝓣).coeffB S) (radA p) := by
      rw [gn, hs]
    rw [e1]
    refine (convergesAt_of_norm_le hradA ((𝓣).norm_coeffB_smallPart_le zero_lt_one d)
      (hd _ hradA radA_lt_one)).2.trans ?_
    have e2 : gaussNorm ((𝓣).coeffB d) (radA p) =
        (𝓣).extNorm b ⟨radA p, radA_pos, hradA_b⟩ ((𝓣).ofAll d hd b) :=
      ((𝓣).extNorm_ofAll hd (σ := b) ⟨radA p, radA_pos, hradA_b⟩).symm
    rw [e2]
    have e3 : (𝓣).ofAll d hd b = rep hx b + -(rep hx b - (𝓣).ofAll d hd b) := by ring
    rw [e3]
    refine ((𝓣).extNorm_add_le _ _ _).trans (max_le_max ?_ ?_)
    · rw [extNorm_rep]
    · rw [(𝓣).extNorm_neg]
      exact (hdapp _ le_rfl).trans ((min_le_right _ _).trans hck1)

end WABridge

end GroundTheory.PAdicHodge
