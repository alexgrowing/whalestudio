import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.ContinuousCut

set_option linter.unusedSectionVars false

noncomputable section

open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.ThKG.Std

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open Classical in

def dl (ν : kˣ →* ℂˣ) (x : k) : ℂ :=
  if h : x ≠ 0 ∧ valuation k x = 1 then (((ν (Units.mk0 x h.1))⁻¹ : ℂˣ) : ℂ) else 0

variable {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}

theorem dl_unit (u : kˣ) (hu : valuation k (u : k) = 1) : dl ν u = (((ν u)⁻¹ : ℂˣ) : ℂ) := by
  rw [dl, dif_pos ⟨u.ne_zero, hu⟩, Units.mk0_val]

theorem dl_of_ne {x : k} (h : valuation k x ≠ 1) : dl ν x = 0 := dif_neg fun h' => h h'.2

theorem dl_ne {x : k} (h : dl ν x ≠ 0) : valuation k x = 1 := by
  by_contra h'; exact h (dl_of_ne h')

theorem exists_unit {x : k} (h : valuation k x = 1) : ∃ u : kˣ, (u : k) = x :=
  ⟨Units.mk0 x (by rintro rfl; simp at h), rfl⟩

theorem dl_one : dl ν (1 : k) = 1 := by simpa using dl_unit (ν := ν) 1 (by simp)

theorem dl_mul_unit {x : k} (hx : valuation k x = 1) (y : k) : dl ν (x * y) = dl ν x * dl ν y := by
  by_cases hy : valuation k y = 1
  · obtain ⟨u, rfl⟩ := exists_unit hx
    obtain ⟨w, rfl⟩ := exists_unit hy
    rw [← Units.val_mul, dl_unit _ (by simp [hx, hy]), dl_unit _ hx, dl_unit _ hy, map_mul, mul_inv, Units.val_mul]
  · rw [dl_of_ne hy, mul_zero, dl_of_ne (by rwa [map_mul, hx, one_mul])]

theorem dl_mul {x y : k} (hx : valuation k x ≤ 1) (hy : valuation k y ≤ 1) : dl ν (x * y) = dl ν x * dl ν y := by
  by_cases h : valuation k x = 1
  · exact dl_mul_unit h y
  · rw [dl_of_ne h, zero_mul, dl_of_ne]
    rw [map_mul]
    exact ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_right' hy) (lt_of_le_of_ne hx h))

theorem val_pow_lt (hϖ : IsUnif ϖ) (hc : 1 ≤ c) : valuation k ((ϖ : k) ^ c) < 1 := by
  rw [map_pow]; exact pow_lt_one₀ zero_le (hϖ ▸ uniformizer_lt_one) (by omega)

theorem val_pow_le (hϖ : IsUnif ϖ) (c : ℕ) : valuation k ((ϖ : k) ^ c) ≤ 1 := by
  rw [map_pow]; exact pow_le_one₀ zero_le (hϖ ▸ uniformizer_lt_one.le)

theorem dl_add (hϖ : IsUnif ϖ) (hc : 1 ≤ c) (hν : CondLE ϖ c ν) (x : k) {t : k} (ht : valuation k t ≤ valuation k ((ϖ : k) ^ c)) :
    dl ν (x + t) = dl ν x := by
  have hl := lt_of_le_of_lt ht (val_pow_lt hϖ hc)
  by_cases hx : valuation k x = 1
  · obtain ⟨u, rfl⟩ := exists_unit hx
    have h1 : valuation k ((u : k)⁻¹ * t) ≤ valuation k ((ϖ : k) ^ c) := by rwa [map_mul, map_inv₀, hx, inv_one, one_mul]
    have h2 : valuation k (1 + (u : k)⁻¹ * t) = 1 := (valuation k).map_one_add_of_lt (h1.trans_lt (val_pow_lt hϖ hc))
    obtain ⟨w, hw⟩ := exists_unit h2
    have : (u : k) + t = u * w := by rw [hw, mul_add, mul_one, mul_inv_cancel_left₀ u.ne_zero]
    rw [this, dl_mul_unit hx, dl_unit w (hw ▸ h2), hν w ⟨hw ▸ h2, by rw [hw]; simpa using h1⟩]
    simp
  · rw [dl_of_ne hx, dl_of_ne]
    intro h
    apply hx
    have := (valuation k).map_sub_eq_of_lt_left (x := x + t) (y := t) (h ▸ hl)
    rwa [add_sub_cancel_right, h] at this

theorem lc_dl (hϖ : IsUnif ϖ) (hc : 1 ≤ c) (hν : CondLE ϖ c ν) : IsLocallyConstant (dl ν) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have h : {t : k | valuation k t ≤ valuation k ((ϖ : k) ^ c)} ∈ 𝓝 (0 : k) :=
    (isClopen_ball (pow_ne_zero _ ϖ.ne_zero)).2.mem_nhds (by simp)
  have h2 : Filter.Tendsto (fun y => y - x) (𝓝 x) (𝓝 0) := by
    have : Continuous fun y : k => y - x := by fun_prop
    simpa using this.tendsto x
  filter_upwards [h2 h] with y hy
  rw [← dl_add hϖ hc hν x hy, add_sub_cancel]

variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] {m : Measure k} {ψ : AddChar k ℂ}

theorem vol_smul (hm : IsVol m) (u : kˣ) (s : Set k) : m (u • s) = ENNReal.ofReal (nabs k u) * m s := by
  haveI := hm.haar
  rw [← distribHaarChar_mul m u s, nabs, ENNReal.ofReal_coe_nnreal]

theorem int_scale (hm : IsVol m) (u : kˣ) (hu : valuation k (u : k) = 1) (f : k → ℂ) : ∫ x, f (u * x) ∂m = ∫ x, f x ∂m := by
  let e : k ≃ᵐ k := (Homeomorph.mulLeft₀ (u : k) u.ne_zero).toMeasurableEquiv
  have hp : MeasurePreserving e m m := by
    refine ⟨e.measurable, Measure.ext fun s hs => ?_⟩
    rw [MeasurableEquiv.map_apply]
    have : e ⁻¹' s = u⁻¹ • s := by
      ext x; rw [Set.mem_inv_smul_set_iff]; rfl
    rw [this, vol_smul hm, nabs_of_valuation_eq_one (by simp [hu])]
    simp
  exact hp.integral_comp' f

theorem int_ind_pow (hm : IsVol m) (hϖ : IsUnif ϖ) (c : ℕ) : ∫ x, ind ((ϖ : k) ^ c) x ∂m = ((resCard k : ℂ) ^ c)⁻¹ := by
  rw [int_ind (pow_ne_zero _ ϖ.ne_zero)]
  have : {x : k | valuation k x ≤ valuation k ((ϖ : k) ^ c)} = (ϖ ^ c) • {x : k | valuation k x ≤ valuation k 1} := by
    ext x
    have h0 : 0 < valuation k ((ϖ : k) ^ c) := zero_lt_iff.2 (by simp)
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_setOf_eq, Units.smul_def, smul_eq_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul,
      map_inv₀, map_one]
    rw [inv_mul_le_iff₀ h0, mul_one]
  have hn : nabs k (ϖ ^ c) = ((resCard k : ℝ) ^ c)⁻¹ := by
    clear this
    induction c with
    | zero => simp [nabs_one]
    | succ c ih => rw [pow_succ, nabs_mul, ih, GlobalTheory.GLDoubling.nabs_unif hϖ, pow_succ, mul_inv]
  rw [Measure.real, this, vol_smul hm, hm.one, mul_one, ENNReal.toReal_ofReal (nabs_pos k _).le, hn]
  simp

def gI (m : Measure k) (ψ : AddChar k ℂ) (ν : kˣ →* ℂˣ) (y : k) : ℂ := ∫ r, dl ν r * ψ (y * r) ∂m

theorem gI_unit (hm : IsVol m) (u : kˣ) (hu : valuation k (u : k) = 1) (y : k) : gI m ψ ν (u * y) = ν u * gI m ψ ν y := by
  rw [gI, gI, ← int_scale hm u hu (fun r => dl ν r * ψ (y * r)), ← integral_const_mul]
  congr 1
  funext r
  rw [dl_mul_unit hu, dl_unit u hu, show y * (u * r) = u * y * r by ring]
  simp [← mul_assoc]

theorem gI_neg (hm : IsVol m) (y : k) : ∫ r, dl ν (-r) * ψ (-(y * r)) ∂m = gI m ψ ν y := by
  rw [gI, ← int_scale hm (-1) (by simp) (fun r => dl ν r * ψ (y * r))]
  simp

theorem gI_small (hm : IsVol m) (hψ : IsPsi ψ) (hϖ : IsUnif ϖ) (hν' : ¬ CondLE ϖ c ν) {y : k}
    (hy : valuation k (y * (ϖ : k) ^ c) ≤ 1) : gI m ψ ν y = 0 := by
  simp only [CondLE, not_forall] at hν'
  obtain ⟨u, ⟨hu, hu'⟩, hne⟩ := hν'
  have : gI m ψ ν (u * y) = gI m ψ ν y := by
    unfold gI
    congr 1
    funext r
    by_cases hr : valuation k r = 1
    · rw [show u * y * r = y * r + y * (u - 1) * r by ring, AddChar.map_add_eq_mul, hψ.triv (x := y * (u - 1) * r), mul_one]
      rw [map_mul, hr, mul_one, map_mul]
      refine le_trans ?_ hy
      rw [map_mul]
      exact mul_le_mul_right (by simpa using hu') _
    · simp [dl_of_ne hr]
  rw [gI_unit hm u hu] at this
  have h2 : ((ν u : ℂ) - 1) * gI m ψ ν y = 0 := by linear_combination this
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 fun h => hne (Units.ext h))

theorem gI_big (hm : IsVol m) (hψ : IsPsi ψ) (hϖ : IsUnif ϖ) (hc : 1 ≤ c) (hν : CondLE ϖ c ν) {y : k}
    (hy : ¬ valuation k (y * (ϖ : k) ^ c) ≤ 1) : gI m ψ ν y = 0 := by
  haveI := hm.haar
  obtain ⟨s, hs, hne⟩ := hψ.ex hy
  have ht : valuation k ((ϖ : k) ^ c * s) ≤ valuation k ((ϖ : k) ^ c) := by rw [map_mul]; exact mul_le_of_le_one_right' hs
  have : gI m ψ ν y = ψ (y * ϖ ^ c * s) * gI m ψ ν y := by
    conv_lhs => rw [gI, ← integral_add_right_eq_self _ ((ϖ : k) ^ c * s)]
    rw [gI, ← integral_const_mul]
    congr 1
    funext r
    rw [dl_add hϖ hc hν r ht, mul_add, AddChar.map_add_eq_mul, mul_assoc y]
    ring
  have h2 : (ψ (y * ϖ ^ c * s) - 1) * gI m ψ ν y = 0 := by linear_combination -this
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)

theorem gI_zero (hm : IsVol m) (hψ : IsPsi ψ) (hϖ : IsUnif ϖ) (hν : CondLE ϖ (c + 1) ν) (hν' : ¬ CondLE ϖ c ν) {y : k}
    (hy : valuation k (y * (ϖ : k) ^ (c + 1)) ≠ 1) : gI m ψ ν y = 0 := by
  by_cases h : valuation k (y * (ϖ : k) ^ (c + 1)) ≤ 1
  · refine gI_small hm hψ hϖ hν' ?_
    have h1 := le_uniformizer_iff.2 (lt_of_le_of_ne h hy)
    rw [← hϖ, pow_succ, ← mul_assoc, map_mul] at h1
    have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
    exact (mul_le_iff_le_one_left h0).1 h1
  · exact gI_big hm hψ hϖ (by omega) hν h

omit [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] in
theorem res_eq_iff (hϖ : IsUnif ϖ) (c : ℕ) (x y : 𝒪[k]) :
    (Ideal.Quotient.mk _ x : Res k c) = Ideal.Quotient.mk _ y ↔ valuation k ((x : k) - y) ≤ valuation k ((ϖ : k) ^ c) := by
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← (Valuation.integer.integers (valuation k)).le_iff_dvd]
  rfl

theorem int_cosets (hm : IsVol m) (hϖ : IsUnif ϖ) (c : ℕ) (f : k → ℂ) (h0 : ∀ x, ¬ valuation k x ≤ 1 → f x = 0)
    (hf : ∀ x t, valuation k t ≤ valuation k ((ϖ : k) ^ c) → f (x + t) = f x) :
    ∫ x, f x ∂m = ((resCard k : ℂ) ^ c)⁻¹ * ∑ᶠ y : Res k c, f ((Quotient.out y : 𝒪[k]) : k) := by
  haveI := hm.haar
  haveI := Fintype.ofFinite (Res k c)
  have e : f = fun x => ∑ y : Res k c, f ((Quotient.out y : 𝒪[k]) : k) * ind ((ϖ : k) ^ c) (x - (Quotient.out y : 𝒪[k])) := by
    funext x
    by_cases hx : valuation k x ≤ 1
    · rw [Finset.sum_eq_single (Ideal.Quotient.mk _ (⟨x, hx⟩ : 𝒪[k]))]
      · have := (res_eq_iff hϖ c ⟨x, hx⟩ _).1 (Ideal.Quotient.mk_out _).symm
        rw [ind, if_pos this, mul_one]
        exact ((hf _ _ this).symm.trans (by rw [add_sub_cancel])).symm
      · intro y _ hy
        rw [ind, if_neg, mul_zero]
        intro h
        exact hy (((res_eq_iff hϖ c ⟨x, hx⟩ _).2 h).trans (Ideal.Quotient.mk_out _)).symm
      · simp
    · rw [h0 x hx]
      refine (Finset.sum_eq_zero fun y _ => ?_).symm
      rw [ind, if_neg, mul_zero]
      intro h
      have := Valuation.map_add_le _ (h.trans (val_pow_le hϖ c)) (Quotient.out y : 𝒪[k]).2
      rw [sub_add_cancel] at this
      exact hx this
  have hi : Integrable (ind ((ϖ : k) ^ c)) m :=
    (lc_ind (pow_ne_zero _ ϖ.ne_zero)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (IsNonarchimedeanLocalField.isCompact_closedBall k (valuation k ((ϖ : k) ^ c)))
        fun x hx => by unfold ind; exact if_neg hx)
  conv_lhs => rw [e]
  rw [integral_finset_sum _ fun y _ => (hi.comp_sub_right _).const_mul _, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_const_mul, integral_sub_right_eq_self, int_ind_pow hm hϖ, mul_comm]

open Classical in
theorem gI_gauss (hm : IsVol m) (hψ : IsPsi ψ) (hϖ : IsUnif ϖ) (hc : 1 ≤ c) (hν : CondLE ϖ c ν) [Fintype (Res k c)ˣ] :
    gI m ψ ν (((ϖ : k) ^ c)⁻¹) = ((resCard k : ℂ) ^ c)⁻¹ * ∑ y : (Res k c)ˣ,
      if h : ((Quotient.out y.1 : 𝒪[k]) : k) = 0 then 0 else
        (((ν (Units.mk0 _ h))⁻¹ : ℂˣ) : ℂ) * ψ (((Quotient.out y.1 : 𝒪[k]) : k) / ϖ ^ c) := by
  have h0 : 0 < valuation k ((ϖ : k) ^ c) := zero_lt_iff.2 (by simp)
  rw [gI, int_cosets hm hϖ c _ (fun x hx => by rw [dl_of_ne fun h => hx h.le, zero_mul]) fun x t ht => by
    rw [dl_add hϖ hc hν x ht, mul_add, AddChar.map_add_eq_mul, hψ.triv (x := _ * t), mul_one]
    rwa [map_mul, map_inv₀, inv_mul_le_iff₀ h0, mul_one]]
  congr 1
  have hu : ∀ y : Res k c, IsUnit y ↔ valuation k ((Quotient.out y : 𝒪[k]) : k) = 1 := fun y => by
    constructor
    · rintro ⟨u, rfl⟩
      have h1 : (Ideal.Quotient.mk _ ((Quotient.out u.1 : 𝒪[k]) * Quotient.out (u⁻¹).1) : Res k c) = Ideal.Quotient.mk _ 1 := by
        rw [map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, Units.mul_inv, map_one]
      have h2 := ((res_eq_iff hϖ c _ _).1 h1).trans_lt (val_pow_lt hϖ hc)
      have h3 := (valuation k).map_one_add_of_lt h2
      simp only [OneMemClass.coe_one, add_sub_cancel, MulMemClass.coe_mul, map_mul] at h3
      refine le_antisymm (Quotient.out u.1 : 𝒪[k]).2 ?_
      rw [← h3]
      exact mul_le_of_le_one_right' (Quotient.out (u⁻¹).1 : 𝒪[k]).2
    · intro h
      have : IsUnit (Quotient.out y : 𝒪[k]) := by
        by_contra h'
        exact absurd h (ne_of_lt (Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 h'))
      simpa only [Ideal.Quotient.mk_out] using this.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))
  symm
  rw [← finsum_eq_sum_of_fintype, ← finsum_mem_univ, finsum_mem_eq_of_bijOn (s := Set.univ) (t := {y | IsUnit y})
    (g := fun y : Res k c => dl ν ((Quotient.out y : 𝒪[k]) : k) * ψ (((ϖ : k) ^ c)⁻¹ * (Quotient.out y : 𝒪[k]))) Units.val
    ⟨fun u _ => u.isUnit, fun _ _ _ _ => Units.ext, fun y ⟨u, hu⟩ => ⟨u, trivial, hu⟩⟩]
  · rw [finsum_mem_def]
    congr 1
    funext y
    by_cases hy : y ∈ {y : Res k c | IsUnit y}
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, dl_of_ne fun h => hy ((hu y).2 h), zero_mul]
  · intro u _
    have h1 := (hu u.1).1 u.isUnit
    have h2 : ((Quotient.out u.1 : 𝒪[k]) : k) ≠ 0 := by intro h; simp [h] at h1
    rw [dif_neg h2, dl, dif_pos ⟨h2, h1⟩, div_eq_inv_mul]

end PositivityTheory.ThKG.Std
