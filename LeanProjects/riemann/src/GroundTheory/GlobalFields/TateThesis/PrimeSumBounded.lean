import Mathlib
import GroundTheory.GlobalFields.TateThesis.Nonvanishing
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes

open NumberField IsDedekindDomain Complex Topology Filter Set

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def primeSum (s : ℝ) : ℂ :=
  ∑' v : HeightOneSpectrum (𝓞 K), χ.coeffTerm (s : ℂ) v.asIdeal

def primeLogSum (s : ℝ) : ℂ :=
  ∑' v : HeightOneSpectrum (𝓞 K), -Complex.log (1 - χ.coeffTerm (s : ℂ) v.asIdeal)

theorem norm_coeffTerm_asIdeal_le {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    ‖χ.coeffTerm (s : ℂ) v.asIdeal‖ ≤ (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  refine (χ.norm_coeffTerm_le _).trans ?_
  have h1 : (1 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
    exact_mod_cast (one_lt_absNorm_asIdeal v).le
  rw [ofReal_re]
  refine inv_anti₀ (by positivity) ?_
  calc (Ideal.absNorm v.asIdeal : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ (1 : ℝ) :=
        (Real.rpow_one _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h1 hs

theorem norm_coeffTerm_asIdeal_le_half {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    ‖χ.coeffTerm (s : ℂ) v.asIdeal‖ ≤ 1 / 2 := by
  refine (χ.norm_coeffTerm_asIdeal_le hs v).trans ?_
  have h2 : (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by exact_mod_cast one_lt_absNorm_asIdeal v
  rw [one_div]
  exact inv_anti₀ two_pos h2

theorem summable_norm_coeffTerm_asIdeal {s : ℝ} (hs : 1 < s) :
    Summable fun v : HeightOneSpectrum (𝓞 K) ↦ ‖χ.coeffTerm (s : ℂ) v.asIdeal‖ :=
  (χ.summable_norm_coeffTerm (by simpa using hs)).comp_injective fun _ _ h ↦ HeightOneSpectrum.ext h

theorem exp_primeLogSum {s : ℝ} (hs : 1 < s) : Complex.exp (χ.primeLogSum s) = χ.LFunction s := by
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  set x : HeightOneSpectrum (𝓞 K) → ℂ := fun v ↦ χ.coeffTerm (s : ℂ) v.asIdeal with hx
  have hlt : ∀ v, ‖x v‖ < 1 := fun v ↦
    (χ.norm_coeffTerm_asIdeal_le_half hs.le v).trans_lt (by norm_num)
  have hne : ∀ v, 1 - x v ≠ 0 := by
    intro v h
    have h1 : x v = 1 := (sub_eq_zero.1 h).symm
    have h2 := hlt v
    rw [h1, norm_one] at h2
    exact lt_irrefl _ h2
  have hxs : Summable x := Summable.of_norm (χ.summable_norm_coeffTerm_asIdeal hs)
  have hlog : Summable fun v ↦ Complex.log (1 - x v) :=
    (Complex.summable_log_one_add_of_summable hxs.neg).congr fun v ↦ by rw [sub_eq_add_neg]
  have hP : HasProd (fun v ↦ 1 - x v) (Complex.exp (∑' v, Complex.log (1 - x v))) :=
    Complex.hasProd_of_hasSum_log hne hlog.hasSum
  have hL : HasProd (fun v ↦ (1 - x v)⁻¹) (χ.LFunction s) := by
    rw [χ.LFunction_eq_tsum_coeffTerm hs']
    exact hasProd_euler _ (χ.summable_norm_coeffTerm hs') (χ.coeffTerm_bot _)
  have h1 := hL.mul hP
  have h2 : (fun v ↦ (1 - x v)⁻¹ * (1 - x v)) = fun _ ↦ (1 : ℂ) :=
    funext fun v ↦ inv_mul_cancel₀ (hne v)
  rw [h2] at h1
  have h3 := h1.unique hasProd_one
  rw [primeLogSum, tsum_neg, Complex.exp_neg]
  exact inv_eq_of_mul_eq_one_left h3

theorem continuousOn_primeLogSum : ContinuousOn χ.primeLogSum (Ioi 1) := by
  intro s₀ hs₀
  have hs₀' : (1 : ℝ) < s₀ := hs₀
  have hσ1 : 1 < (1 + s₀) / 2 := by linarith
  have hσs : (1 + s₀) / 2 < s₀ := by linarith
  have hc : ContinuousOn χ.primeLogSum (Ioi ((1 + s₀) / 2)) := by
    refine continuousOn_tsum
      (u := fun v : HeightOneSpectrum (𝓞 K) ↦
        3 / 2 * ((Ideal.absNorm v.asIdeal : ℝ) ^ ((1 + s₀) / 2))⁻¹) (fun v ↦ ?_) ?_
      (fun v s hs ↦ ?_)
    · have hN : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
        exact_mod_cast (one_pos.trans (one_lt_absNorm_asIdeal v)).ne'
      intro s hs
      have hs1 : (1 : ℝ) ≤ s := by
        have : (1 + s₀) / 2 < s := hs
        linarith
      refine ContinuousAt.continuousWithinAt ?_
      have hcp : ContinuousAt (fun t : ℝ ↦ (Ideal.absNorm v.asIdeal : ℂ) ^ (t : ℂ)) s :=
        (continuous_ofReal.const_cpow (Or.inl hN)).continuousAt
      have hden : (Ideal.absNorm v.asIdeal : ℂ) ^ (s : ℂ) ≠ 0 := fun h ↦
        hN ((cpow_eq_zero_iff _ _).1 h).1
      have hterm : ContinuousAt (fun t : ℝ ↦ χ.coeffTerm (t : ℂ) v.asIdeal) s := by
        simp only [coeffTerm_apply]
        exact continuousAt_const.div hcp hden
      refine (ContinuousAt.clog (continuousAt_const.sub hterm) ?_).neg
      have hm := mem_slitPlane_of_norm_lt_one (z := -χ.coeffTerm (s : ℂ) v.asIdeal)
        (by rw [norm_neg]; exact (χ.norm_coeffTerm_asIdeal_le_half hs1 v).trans_lt (by norm_num))
      rwa [← sub_eq_add_neg] at hm
    · exact ((summable_absNorm_rpow_inv hσ1).comp_injective
        fun _ _ h ↦ HeightOneSpectrum.ext h).mul_left _
    · have hs' : (1 + s₀) / 2 < s := hs
      have hs1 : (1 : ℝ) ≤ s := by linarith
      have h1 : (1 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
        exact_mod_cast (one_lt_absNorm_asIdeal v).le
      rw [norm_neg, sub_eq_add_neg]
      refine (norm_log_one_add_half_le_self
        (by rw [norm_neg]; exact χ.norm_coeffTerm_asIdeal_le_half hs1 v)).trans ?_
      rw [norm_neg]
      refine mul_le_mul_of_nonneg_left ((χ.norm_coeffTerm_le _).trans ?_) (by norm_num)
      rw [ofReal_re]
      exact inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le h1 hs'.le)
  exact (hc.continuousAt (Ioi_mem_nhds hσs)).continuousWithinAt

theorem exists_tendsto_primeLogSum {L₁ : ℂ} (hL₁ : L₁ ≠ 0)
    (hL : Tendsto (fun s : ℝ ↦ χ.LFunction s) (𝓝[>] 1) (𝓝 L₁)) :
    ∃ c : ℂ, Tendsto χ.primeLogSum (𝓝[>] 1) (𝓝 c) := by
  have hw1 : Tendsto (fun s : ℝ ↦ χ.LFunction s / L₁) (𝓝[>] 1) (𝓝 1) := by
    have := hL.div_const L₁
    rwa [div_self hL₁] at this
  have hball : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), χ.LFunction s / L₁ ∈ Metric.ball (1 : ℂ) 1 :=
    hw1 (Metric.ball_mem_nhds _ one_pos)
  obtain ⟨u, hu1, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hball
  have hu1' : (1 : ℝ) < u := hu1
  have hslit : ∀ s ∈ Ioo (1 : ℝ) u, χ.LFunction s / L₁ ∈ slitPlane := fun s hs ↦ by
    have h : χ.LFunction s / L₁ ∈ Metric.ball (1 : ℂ) 1 := hu hs
    rw [Metric.mem_ball, dist_eq_norm] at h
    have := mem_slitPlane_of_norm_lt_one h
    rwa [add_sub_cancel] at this
  have hLc : ∀ s ∈ Ioo (1 : ℝ) u, ContinuousAt (fun s : ℝ ↦ χ.LFunction s) s := fun s hs ↦ by
    have hs' : 1 < ((s : ℝ) : ℂ).re := by simpa using hs.1
    have hd := (χ.differentiableOn_LFunction _ hs').differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds hs')
    exact hd.continuousAt.comp continuous_ofReal.continuousAt
  have hs₀ : (1 + u) / 2 ∈ Ioo (1 : ℝ) u := ⟨by linarith, by linarith⟩
  set s₀ := (1 + u) / 2
  set c := χ.primeLogSum s₀ - Complex.log (χ.LFunction s₀ / L₁) with hc
  have heq : EqOn χ.primeLogSum (fun s : ℝ ↦ Complex.log (χ.LFunction s / L₁) + c) (Ioo 1 u) := by
    refine isCoveringMap_exp.eqOn_of_comp_eqOn isPreconnected_Ioo
      (χ.continuousOn_primeLogSum.mono fun s hs ↦ hs.1)
      (fun s hs ↦ ((ContinuousAt.clog ((hLc s hs).div_const L₁) (hslit s hs)).add
        continuousAt_const).continuousWithinAt) (fun s hs ↦ ?_) hs₀ (by rw [hc]; ring)
    apply Subtype.ext
    simp only [Function.comp_apply]
    rw [Complex.exp_add, Complex.exp_log (slitPlane_ne_zero (hslit s hs)), hc, Complex.exp_sub,
      Complex.exp_log (slitPlane_ne_zero (hslit s₀ hs₀)), χ.exp_primeLogSum hs.1,
      χ.exp_primeLogSum hs₀.1]
    have h0 : χ.LFunction s₀ ≠ 0 := χ.LFunction_ne_zero (by simpa using hs₀.1)
    field_simp
  refine ⟨c, ?_⟩
  have hlim : Tendsto (fun s : ℝ ↦ Complex.log (χ.LFunction s / L₁) + c) (𝓝[>] 1)
      (𝓝 (Complex.log 1 + c)) :=
    ((continuousAt_clog (by simp)).tendsto.comp hw1).add tendsto_const_nhds
  rw [Complex.log_one, zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hu1'] with s hs using (heq hs).symm

theorem isBoundedUnder_norm_primeSum {L₁ : ℂ} (hL₁ : L₁ ≠ 0)
    (hL : Tendsto (fun s : ℝ ↦ χ.LFunction s) (𝓝[>] 1) (𝓝 L₁)) :
    IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s ↦ ‖χ.primeSum s‖ := by
  obtain ⟨c, hc⟩ := χ.exists_tendsto_primeLogSum hL₁ hL
  have hB : Summable fun v : HeightOneSpectrum (𝓞 K) ↦
      ((Ideal.absNorm v.asIdeal : ℝ) ^ (2 : ℝ))⁻¹ :=
    (summable_absNorm_rpow_inv (K := K) one_lt_two).comp_injective
      fun _ _ h ↦ HeightOneSpectrum.ext h
  set B := ∑' v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ℝ) ^ (2 : ℝ))⁻¹
  have hnear : ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖χ.primeLogSum s‖ ≤ ‖c‖ + 1 := by
    filter_upwards [hc.norm.eventually (gt_mem_nhds (lt_add_one ‖c‖))] with s hs using hs.le
  refine isBoundedUnder_of_eventually_le (a := ‖c‖ + 1 + B) ?_
  filter_upwards [hnear, self_mem_nhdsWithin] with s hs hs1
  have hs1' : (1 : ℝ) < s := hs1
  have hdiff : ‖χ.primeLogSum s - χ.primeSum s‖ ≤ B := by
    have hP : Summable fun v : HeightOneSpectrum (𝓞 K) ↦ χ.coeffTerm (s : ℂ) v.asIdeal :=
      Summable.of_norm (χ.summable_norm_coeffTerm_asIdeal hs1')
    have hF : Summable fun v : HeightOneSpectrum (𝓞 K) ↦
        -Complex.log (1 - χ.coeffTerm (s : ℂ) v.asIdeal) := by
      refine Summable.of_norm_bounded ((χ.summable_norm_coeffTerm_asIdeal hs1').mul_left (3 / 2))
        fun v ↦ ?_
      rw [norm_neg, sub_eq_add_neg]
      refine (norm_log_one_add_half_le_self
        (by rw [norm_neg]; exact χ.norm_coeffTerm_asIdeal_le_half hs1'.le v)).trans ?_
      rw [norm_neg]
    rw [primeLogSum, primeSum, ← hF.tsum_sub hP]
    refine tsum_of_norm_bounded hB.hasSum fun v ↦ ?_
    set a := χ.coeffTerm (s : ℂ) v.asIdeal
    have ha := χ.norm_coeffTerm_asIdeal_le_half hs1'.le v
    have ha' := χ.norm_coeffTerm_asIdeal_le hs1'.le v
    have e : -Complex.log (1 - a) - a = -(Complex.log (1 + -a) - -a) := by
      rw [sub_eq_add_neg 1 a]
      ring
    rw [e, norm_neg]
    refine (norm_log_one_add_sub_self_le (by rw [norm_neg]; linarith)).trans ?_
    rw [norm_neg]
    have ht0 : 0 ≤ ‖a‖ := norm_nonneg _
    have hinv : (1 - ‖a‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) two_pos]
      linarith
    have hN0 : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
      exact_mod_cast one_pos.trans (one_lt_absNorm_asIdeal v)
    calc ‖a‖ ^ 2 * (1 - ‖a‖)⁻¹ / 2 ≤ ‖a‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖a‖ ^ 2 := by ring
      _ ≤ ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ 2 := by gcongr
      _ = ((Ideal.absNorm v.asIdeal : ℝ) ^ (2 : ℝ))⁻¹ := by rw [Real.rpow_two, inv_pow]
  calc ‖χ.primeSum s‖ = ‖χ.primeLogSum s - (χ.primeLogSum s - χ.primeSum s)‖ := by
        rw [sub_sub_cancel]
    _ ≤ ‖χ.primeLogSum s‖ + ‖χ.primeLogSum s - χ.primeSum s‖ := norm_sub_le _ _
    _ ≤ ‖c‖ + 1 + B := add_le_add hs hdiff

theorem not_exists_cpow_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) (hχn : χ ^ n = 1) (hχ : χ ≠ 1) :
    ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I) := by
  rintro ⟨τ, hτ⟩
  have h0 : τ * n = 0 := by
    refine eq_zero_of_forall_ideleModule_cpow_eq_one (K := K) fun x ↦ ?_
    have h1 : (((χ ^ n).toIdele x : Circle) : ℂ) = 1 := by
      rw [hχn, toIdele_apply]
      rfl
    rw [pow_toIdele, Circle.coe_pow, hτ x, ← cpow_nat_mul] at h1
    rw [← h1]
    push_cast
    ring_nf
  have hτ0 : τ = 0 := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact h
    · exact absurd (by exact_mod_cast h) hn
  apply hχ
  ext c
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  have h := hτ x
  rw [hτ0, ofReal_zero, zero_mul, cpow_zero, toIdele_apply] at h
  rw [h]
  rfl

theorem exists_tendsto_LFunction_of_not_exists
    (hχ : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) :
    ∃ L₁ : ℂ, L₁ ≠ 0 ∧ Tendsto (fun s : ℝ ↦ χ.LFunction s) (𝓝[>] 1) (𝓝 L₁) := by
  obtain ⟨G, hG, hGL⟩ := χ.exists_LFunction_continuation hχ
  refine ⟨G 1, χ.continuation_ne_zero_of_one_le_re hχ hG hGL (by simp), ?_⟩
  have h1 : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) := by
    have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 1))
    rwa [ofReal_one] at this
  refine ((hG 1).continuousAt.tendsto.comp h1).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact hGL s (by simpa using hs)

theorem isBoundedUnder_norm_primeSum_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) (hχn : χ ^ n = 1)
    (hχ : χ ≠ 1) : IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s ↦ ‖χ.primeSum s‖ := by
  obtain ⟨L₁, hL₁, hL⟩ :=
    χ.exists_tendsto_LFunction_of_not_exists (χ.not_exists_cpow_of_pow_eq_one hn hχn hχ)
  exact χ.isBoundedUnder_norm_primeSum hL₁ hL

end HeckeCharacter

end

end GroundTheory.Global
