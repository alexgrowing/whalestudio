import Mathlib
import GroundTheory.PAdicHodge.BCrisNewtonNorm
import GroundTheory.PAdicHodge.ACrisBdRInj
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WittTilt

open _root_.WittVector Laurent ACris

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p

theorem exists_approx (a : ACris K p) (N : ℕ) :
    ∃ c : ACrisZero K p, a - algebraMap _ (ACris K p) c ∈ Ideal.span {(p : ACris K p) ^ N} := by
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective
    (_root_.AdicCompletion.evalₐ (Ideal.span {(p : ACrisZero K p)}) N a)
  refine ⟨c, ?_⟩
  have h : a - _root_.AdicCompletion.of _ _ c ∈
      (Ideal.span {(p : ACrisZero K p)} ^ N).map (algebraMap (ACrisZero K p) (ACris K p)) := by
    rw [← ker_adicCompletion_evalₐ (Submodule.fg_span_singleton _), RingHom.mem_ker]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub]
    rw [← hc]
    exact sub_eq_zero.2 (_root_.AdicCompletion.evalₐ_of _ N c).symm
  rwa [span_p_pow_map, Ideal.span_singleton_pow] at h

theorem exists_eq_pow_mul_of_mem {c₁ c₂ : ACrisZero K p} {N : ℕ}
    (h : algebraMap _ (ACris K p) c₁ - algebraMap _ (ACris K p) c₂ ∈
      Ideal.span {(p : ACris K p) ^ N}) :
    ∃ z : ACrisZero K p, c₁ - c₂ = (p : ACrisZero K p) ^ N * z := by
  rw [← Ideal.span_singleton_pow, ← span_p_pow_map, ← map_sub,
    ← ker_adicCompletion_evalₐ (Submodule.fg_span_singleton _), RingHom.mem_ker] at h
  have h2 : Ideal.Quotient.mk (Ideal.span {(p : ACrisZero K p)} ^ N) (c₁ - c₂) = 0 := by
    rw [← _root_.AdicCompletion.evalₐ_of]
    exact h
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
  exact h2

variable {ρ : ℝ}

theorem gn_p_pow_mul (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ) (z : 𝔸) :
    gn K p ρ ((p : 𝔸) ^ N * z) = ρ ^ N * gn K p ρ z := by
  rw [gn_mul hρ0 hρ1, gn_pow hρ0 hρ1, gn_natCast_p hρ0]

theorem gn_sub_le_of_mem (hp0 : ‖(p : K)‖ ≤ ρ) (hρ1 : ρ < 1) {c₁ c₂ : ACrisZero K p} {N : ℕ}
    (h : algebraMap _ (ACris K p) c₁ - algebraMap _ (ACris K p) c₂ ∈
      Ideal.span {(p : ACris K p) ^ N}) :
    gn K p ρ ((c₁ : 𝔸) - c₂) ≤ ρ ^ N := by
  have hρ0 : 0 < ρ := norm_p_pos.trans_le hp0
  obtain ⟨z, hz⟩ := exists_eq_pow_mul_of_mem h
  have e : (c₁ : 𝔸) - c₂ = (p : 𝔸) ^ N * z := by
    rw [← Subalgebra.coe_sub, hz]; simp
  rw [e, gn_p_pow_mul hρ0 hρ1]
  exact mul_le_of_le_one_right (pow_nonneg hρ0.le N) (gn_acrisZero_le_one hp0 hρ0 hρ1 z.2)

theorem gn_eq_of_gn_sub_lt (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {z w : 𝔸}
    (h : gn K p ρ (z - w) < gn K p ρ z) : gn K p ρ w = gn K p ρ z := by
  apply le_antisymm
  · have := gn_sub_le (K := K) hρ0 hρ1 z (z - w)
    rw [sub_sub_cancel] at this
    exact this.trans (max_le le_rfl h.le)
  · have := gn_add_le (K := K) hρ0 hρ1 (z - w) w
    rw [sub_add_cancel] at this
    rcases le_max_iff.1 this with h1 | h1
    · exact absurd h1 (not_le.2 h)
    · exact h1

theorem le_gn_of_ker_eq_span {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ}) :
    ‖(p : K)‖ ≤ gn K p ‖(p : K)‖ (algebraMap (AInf K p) 𝔸 ξ) := by
  set r₀ := ‖(p : K)‖ with hr₀
  obtain ⟨w, hw⟩ := exists_norm_untilt_eq_norm_natCast (K := K) (p := p)
  set u : K := ((PreTilt.untilt w : 𝒪) : K) / p with hu_def
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hr0 : 0 < ‖(p : K)‖ := norm_p_pos
  have hr1 : ‖(p : K)‖ < 1 := norm_p_lt_one
  have hu : ‖u‖ ≤ 1 := by rw [hu_def, norm_div, hw, div_self hr0.ne']
  obtain ⟨v, hv⟩ := IsPerfectoidField.surjective_fontaineTheta (K := K) (p := p)
    ⟨u, mem_normInteger.2 hu⟩
  have hker : teichmuller p w - (p : AInf K p) * v ∈ RingHom.ker θ := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_natCast, fontaineTheta_teichmuller, hv]
    apply Subtype.ext
    push_cast
    rw [hu_def]
    field_simp
    ring
  rw [hξ] at hker
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hker
  have h0 : (teichmuller p w - (p : AInf K p) * v).coeff 0 = w := by
    show WittVector.constantCoeff (teichmuller p w - (p : AInf K p) * v) = w
    rw [map_sub, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, sub_zero]
    exact teichmuller_coeff_zero p w
  have hlow : r₀ ≤ gn K p r₀ (algebraMap (AInf K p) 𝔸 (teichmuller p w - (p : AInf K p) * v)) := by
    rw [gn_algebraMap]
    have := (convergesAt_zcoeff_incl (teichmuller p w - (p : AInf K p) * v) hr0
      hr1).le_gaussNorm 0
    rw [zcoeff_incl_zero, h0, norm_algebraMap_preTilt, zpow_zero, mul_one, preTilt_norm_def, hw] at this
    exact this
  rw [← hz, map_mul, gn_mul hr0 hr1] at hlow
  exact hlow.trans (mul_le_of_le_one_left (gn_nonneg hr0 _)
    (gn_algebraMap_le_one hr0 hr1.le z))

theorem exists_iotaQ_ne_zero {a : ACris K p} (ha : a ≠ 0) : ∃ m, iotaQ K p (m + 1) a ≠ 0 := by
  by_contra h
  push_neg at h
  apply ha
  apply iota_injective (K := K) (p := p)
  rw [map_zero]
  show @Eq (_root_.AdicCompletion (kerAway K p) 𝔸) (iota K p a) 0
  refine _root_.AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_iota, map_zero]
  rcases n with _ | m
  · rw [← iotaQ_compat (Nat.zero_le 1), RingHom.comp_apply, h 0, map_zero]
  · exact h m

set_option maxHeartbeats 1600000 in

theorem exists_lower_bound {a : ACris K p} (ha : a ≠ 0) :
    ∃ (B : ℝ) (N₀ : ℕ), 0 < B ∧ ∀ N ≥ N₀, ∀ c : ACrisZero K p,
      a - algebraMap _ (ACris K p) c ∈ Ideal.span {(p : ACris K p) ^ N} →
        B < gn K p ‖(p : K)‖ (c : 𝔸) := by
  set r₀ := ‖(p : K)‖ with hr₀
  have hr0 : 0 < r₀ := norm_p_pos
  have hr1 : r₀ < 1 := norm_p_lt_one
  obtain ⟨m, hm⟩ := exists_iotaQ_ne_zero ha
  set Q := 𝔸 ⧸ kerAway K p ^ (m + 1)
  set v := (m + 1 - 1).factorial.factorization p with hv
  have hx : (p : Q) ^ v * iotaQ K p (m + 1) a ∈ latticeQ K p (m + 1) :=
    pow_mul_mem_latticeQ (m + 1) _ (embedding₂ K p (m + 1) a).2
  set x : latticeQ K p (m + 1) := ⟨_, hx⟩ with hx_def
  have hx0 : x ≠ 0 := by
    intro h0
    apply hm
    have h1 : (p : Q) ^ v * iotaQ K p (m + 1) a = 0 := congrArg Subtype.val h0
    exact ((isUnit_p_quot (K := K) (p := p) (m + 1)).pow v).mul_right_eq_zero.1 h1
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, ¬ ∃ w : latticeQ K p (m + 1),
      x = (p : latticeQ K p (m + 1)) ^ k₀ * w := by
    by_contra h
    push_neg at h
    apply hx0
    refine IsHausdorff.haus' (I := Ideal.span {(p : latticeQ K p (m + 1))}) x fun n => ?_
    obtain ⟨w, hw⟩ := h n
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨w, hw⟩
  refine ⟨r₀ ^ (k₀ + v + m), k₀, pow_pos hr0 _, fun N hN c hc => ?_⟩
  by_contra hle
  push_neg at hle
  obtain ⟨M, c', hc'⟩ := IsLocalization.Away.surj (p : AInf K p) (c : 𝔸)
  rw [map_natCast] at hc'
  have hgc' : gn K p r₀ (algebraMap _ 𝔸 c') ≤ r₀ ^ ((k₀ + v + M) + m) := by
    rw [← hc', mul_comm, gn_p_pow_mul hr0 hr1]
    calc r₀ ^ M * gn K p r₀ (c : 𝔸) ≤ r₀ ^ M * r₀ ^ (k₀ + v + m) :=
          mul_le_mul_of_nonneg_left hle (pow_nonneg hr0.le M)
      _ = r₀ ^ ((k₀ + v + M) + m) := by rw [← pow_add]; congr 1; ring
  obtain ⟨w, z, hwz⟩ := exists_eq_pow_mul_add_xi_pow_mul ker_eq_span_xiGen
    (le_gn_of_ker_eq_span ker_eq_span_xiGen) m (k₀ + v + M) c' hgc'
  have hmk : Ideal.Quotient.mk (kerAway K p ^ (m + 1)) (c : 𝔸) =
      (p : Q) ^ (k₀ + v) * Ideal.Quotient.mk (kerAway K p ^ (m + 1)) (algebraMap _ 𝔸 w) := by
    have hz0 : Ideal.Quotient.mk (kerAway K p ^ (m + 1))
        (algebraMap (AInf K p) 𝔸 (xiGen K p ^ (m + 1) * z)) = 0 := by
      rw [mk_eq_zero_iff, map_mul]; exact dvd_mul_right _ _
    have e1 : Ideal.Quotient.mk (kerAway K p ^ (m + 1)) (c : 𝔸) * (p : Q) ^ M =
        (p : Q) ^ M * ((p : Q) ^ (k₀ + v) * Ideal.Quotient.mk (kerAway K p ^ (m + 1)) (algebraMap _ 𝔸 w)) := by
      have := congrArg (Ideal.Quotient.mk (kerAway K p ^ (m + 1))) hc'
      rw [map_mul, map_pow, map_natCast] at this
      rw [this, hwz, map_add, map_add, hz0, add_zero]
      simp only [map_mul, map_pow, map_natCast]
      ring
    rw [mul_comm] at e1
    exact ((isUnit_p_quot (K := K) (p := p) (m + 1)).pow M).mul_left_cancel e1
  obtain ⟨α, hα⟩ := Ideal.mem_span_singleton'.1 hc
  have hiota : iotaQ K p (m + 1) a = Ideal.Quotient.mk (kerAway K p ^ (m + 1)) (c : 𝔸) +
      (p : Q) ^ N * iotaQ K p (m + 1) α := by
    have := congrArg (iotaQ K p (m + 1)) hα
    rw [map_mul, map_pow, map_natCast, map_sub,
      show algebraMap (ACrisZero K p) (ACris K p) c = _root_.AdicCompletion.of _ _ c from rfl,
      iotaQ_of] at this
    linear_combination -this
  apply hk₀
  have hαL : (p : Q) ^ v * iotaQ K p (m + 1) α ∈ latticeQ K p (m + 1) :=
    pow_mul_mem_latticeQ (m + 1) _ (embedding₂ K p (m + 1) α).2
  have hwL : Ideal.Quotient.mk (kerAway K p ^ (m + 1)) (algebraMap _ 𝔸 w) ∈ latticeQ K p (m + 1) :=
    ⟨w, rfl⟩
  have hpL : (p : Q) ∈ latticeQ K p (m + 1) := natCast_mem _ p
  refine ⟨⟨(p : Q) ^ (2 * v) * Ideal.Quotient.mk (kerAway K p ^ (m + 1)) (algebraMap _ 𝔸 w) +
    (p : Q) ^ (N - k₀) * ((p : Q) ^ v * iotaQ K p (m + 1) α),
    add_mem (mul_mem (pow_mem hpL _) hwL) (mul_mem (pow_mem hpL _) hαL)⟩, ?_⟩
  apply Subtype.ext
  simp only [hx_def, MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
  have hpN : (p : Q) ^ N = (p : Q) ^ k₀ * (p : Q) ^ (N - k₀) := by
    rw [← pow_add]; congr 1; omega
  rw [hiota, hmk, hpN]
  ring

set_option maxHeartbeats 1600000 in

theorem exists_stable {a : ACris K p} (ha : a ≠ 0) :
    ∃ (ρ₂ : ℝ) (N₀ : ℕ) (c₀ : ACrisZero K p), ‖(p : K)‖ < ρ₂ ∧ ρ₂ < 1 ∧
      a - algebraMap _ (ACris K p) c₀ ∈ Ideal.span {(p : ACris K p) ^ N₀} ∧
      (∀ ρ ∈ Set.Icc ‖(p : K)‖ ρ₂, ρ ^ N₀ < gn K p ρ (c₀ : 𝔸)) ∧
      ∀ N ≥ N₀, ∀ c : ACrisZero K p,
        a - algebraMap _ (ACris K p) c ∈ Ideal.span {(p : ACris K p) ^ N} →
          ∀ ρ ∈ Set.Icc ‖(p : K)‖ ρ₂, gn K p ρ (c : 𝔸) = gn K p ρ (c₀ : 𝔸) := by
  set r₀ := ‖(p : K)‖ with hr₀
  have hr0 : 0 < r₀ := norm_p_pos
  have hr1 : r₀ < 1 := norm_p_lt_one
  obtain ⟨B, N₁, hB, hbound⟩ := exists_lower_bound ha
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hB hr1
  set N₀ := max N₁ n
  have hN₀ : r₀ ^ N₀ < B := (pow_le_pow_of_le_one hr0.le hr1.le (le_max_right N₁ n)).trans_lt hn
  obtain ⟨c₀, hc₀⟩ := exists_approx a N₀
  have hlow : r₀ ^ N₀ < gn K p r₀ (c₀ : 𝔸) := hN₀.trans (hbound N₀ (le_max_left _ _) c₀ hc₀)

  have hne : (teichLift K p).coeffB (toB K p (c₀ : 𝔸)) ≠ 0 := by
    intro h
    have h2 : gn K p r₀ (c₀ : 𝔸) = 0 := by unfold gn; rw [h]; simp [gaussNorm]
    linarith [pow_pos hr0 N₀]
  obtain ⟨i, hi⟩ := (convergesAt_toB (K := K) (c₀ : 𝔸) hr0 hr1).exists_eq_gaussNorm hr0 hne
  set β := ‖(teichLift K p).coeffB (toB K p (c₀ : 𝔸)) i‖
  have hf : ContinuousAt (fun ρ : ℝ => β * ρ ^ i - ρ ^ N₀) r₀ :=
    ((continuousAt_const.mul (continuousAt_zpow₀ r₀ i (Or.inl hr0.ne'))).sub
      (continuousAt_id.pow N₀))
  have hf0 : 0 < β * r₀ ^ i - r₀ ^ N₀ := by
    have : β * r₀ ^ i = gn K p r₀ (c₀ : 𝔸) := hi
    linarith
  obtain ⟨δ, hδ, hδf⟩ := Metric.eventually_nhds_iff.1 (hf.eventually (lt_mem_nhds hf0))
  set ρ₂ := min (r₀ + δ / 2) ((r₀ + 1) / 2)
  have hρ₂a : r₀ < ρ₂ := lt_min (by linarith) (by linarith)
  have hρ₂b : ρ₂ < 1 := (min_le_right _ _).trans_lt (by linarith)
  have hIcc : ∀ ρ ∈ Set.Icc r₀ ρ₂, 0 < ρ ∧ ρ < 1 ∧ r₀ ≤ ρ ∧ ρ ^ N₀ < β * ρ ^ i := by
    intro ρ hρ
    refine ⟨hr0.trans_le hρ.1, hρ.2.trans_lt hρ₂b, hρ.1, ?_⟩
    have hd : dist ρ r₀ < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hρ.1])]
      linarith [hρ.2, min_le_left (r₀ + δ / 2) ((r₀ + 1) / 2)]
    have : 0 < β * ρ ^ i - ρ ^ N₀ := hδf hd
    linarith
  have hgood : ∀ ρ ∈ Set.Icc r₀ ρ₂, ρ ^ N₀ < gn K p ρ (c₀ : 𝔸) := by
    intro ρ hρ
    obtain ⟨h0, h1, -, h2⟩ := hIcc ρ hρ
    exact h2.trans_le ((convergesAt_toB (K := K) (c₀ : 𝔸) h0 h1).le_gaussNorm i)
  refine ⟨ρ₂, N₀, c₀, hρ₂a, hρ₂b, hc₀, hgood, fun N hN c hc ρ hρ => ?_⟩
  obtain ⟨h0, h1, hpρ, -⟩ := hIcc ρ hρ
  have hsub : algebraMap _ (ACris K p) c₀ - algebraMap _ (ACris K p) c ∈
      Ideal.span {(p : ACris K p) ^ N₀} := by
    have hc' : a - algebraMap _ (ACris K p) c ∈ Ideal.span {(p : ACris K p) ^ N₀} :=
      Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hN) hc
    have := sub_mem hc' hc₀
    rwa [sub_sub_sub_cancel_left] at this
  have hle := gn_sub_le_of_mem hpρ h1 hsub
  exact gn_eq_of_gn_sub_lt h0 h1 (hle.trans_lt (hgood ρ hρ))

end WittTilt

end GroundTheory.PAdicHodge
