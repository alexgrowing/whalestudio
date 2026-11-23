import Mathlib

open UpperHalfPlane ModularForm MatrixGroups EisensteinSeries Filter Topology

namespace GlobalTheory.DiscUniformisation

lemma tendsto_coeff_zero {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Tendsto f atImInfty (𝓝 ((qExpansion 1 f).coeff 0)) := by
  have hp := one_mem_strictPeriods_SL
  have han := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hp
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hp
  rw [UpperHalfPlane.qExpansion_coeff_zero one_pos han hper,
    ← UpperHalfPlane.cuspFunction_apply_zero one_pos han hper]
  refine (han.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)).congr
    fun τ => ?_
  exact UpperHalfPlane.eq_cuspFunction τ one_ne_zero hper

lemma tendsto_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) : Tendsto (E hk) atImInfty (𝓝 1) := by
  have h := tendsto_coeff_zero (E hk)
  rwa [EisensteinSeries.E_qExpansion_coeff_zero hk hk2] at h

lemma exists_zero (F : ModularForm 𝒮ℒ 12) (c : ℂ) (hc : c ≠ 0)
    (hF : Tendsto F atImInfty (𝓝 c)) : ∃ z, F z = 0 := by
  by_contra hne
  push_neg at hne

  have hD0 : Tendsto ModularForm.discriminant atImInfty (𝓝 0) := by
    have h1 := tendsto_coeff_zero (ModularFormClass.modularForm CuspForm.discriminant)
    rw [ModularFormClass.coe_modularForm,
      CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL,
      CuspForm.coe_discriminant] at h1
    exact h1
  have hG0 : Tendsto (fun τ => ModularForm.discriminant τ / F τ) atImInfty (𝓝 0) := by
    have h := hD0.div hF hc
    rw [zero_div] at h
    exact h

  let G0 : SlashInvariantForm 𝒮ℒ 0 :=
    { toFun := fun τ => ModularForm.discriminant τ / F τ
      slash_action_eq' := by
        rintro γ ⟨g, rfl⟩
        funext τ
        have key : SlashAction.map (0 : ℤ) g (fun τ => ModularForm.discriminant τ / F τ) τ =
            ModularForm.discriminant τ / F τ := by
          rw [ModularForm.slash_action_eq'_iff, zpow_zero, one_mul]
          have hΔ := (ModularForm.slash_action_eq'_iff 12 (⇑CuspForm.discriminant) g τ).1
            (congrFun (SlashInvariantForm.slash_action_eqn CuspForm.discriminant _ ⟨g, rfl⟩) τ)
          have hF' := (ModularForm.slash_action_eq'_iff 12 (⇑F) g τ).1
            (congrFun (SlashInvariantForm.slash_action_eqn F _ ⟨g, rfl⟩) τ)
          rw [CuspForm.coe_discriminant] at hΔ
          show ModularForm.discriminant (g • τ) / F (g • τ) = ModularForm.discriminant τ / F τ
          have hd : ∀ x : ℂ, ModularForm.discriminant (g • τ) = x * ModularForm.discriminant τ → x ≠ 0 := by
            rintro x hx rfl
            rw [zero_mul] at hx
            exact ModularForm.discriminant_ne_zero _ hx
          have hx0 := hd _ hΔ
          rw [hΔ, hF']
          rw [mul_div_mul_left _ _ hx0]
        exact key }
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty G0.toFun :=
    UpperHalfPlane.IsZeroAtImInfty.isBoundedAtImInfty hG0
  let G : ModularForm 𝒮ℒ 0 :=
    { toSlashInvariantForm := G0
      holo' := (ModularFormClass.holo CuspForm.discriminant).div (ModularFormClass.holo F) hne
      bdd_at_cusps' := by
        intro c' hc'
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc']
        intro γ _
        convert hbdd using 1
        exact G0.slash_action_eq' _ ⟨γ, rfl⟩ }
  obtain ⟨c', hc'⟩ := ModularForm.eq_const_of_weight_zero G
  have hGt : Tendsto (⇑G) atImInfty (𝓝 0) := hG0
  rw [hc'] at hGt
  have hc0 : c' = 0 := tendsto_nhds_unique tendsto_const_nhds hGt
  have h1 : G UpperHalfPlane.I = 0 := by rw [hc', Function.const_apply, hc0]
  have h2 : ModularForm.discriminant UpperHalfPlane.I / F UpperHalfPlane.I = 0 := h1
  rcases div_eq_zero_iff.1 h2 with h3 | h3
  · exact ModularForm.discriminant_ne_zero _ h3
  · exact hne _ h3

lemma E_cube_ne (z : ℍ) : E₄ z ^ 3 ≠ E₆ z ^ 2 := by
  intro h
  apply ModularForm.discriminant_ne_zero z
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, h, sub_self, zero_div]

lemma exists_ratio (A B : ℂ) (h : A ^ 3 ≠ B ^ 2) :
    ∃ z : ℍ, B ^ 2 * E₄ z ^ 3 = A ^ 3 * E₆ z ^ 2 := by
  let F4 : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by norm_num) (E₄.mul (E₄.mul E₄))
  let F6 : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by norm_num) (E₆.mul E₆)
  let F : ModularForm 𝒮ℒ 12 := B ^ 2 • F4 - A ^ 3 • F6
  have hF : ∀ z, F z = B ^ 2 * E₄ z ^ 3 - A ^ 3 * E₆ z ^ 2 := by
    intro z
    show B ^ 2 * (E₄ z * (E₄ z * E₄ z)) - A ^ 3 * (E₆ z * E₆ z) = _
    ring
  have t4 : Tendsto (⇑E₄) atImInfty (𝓝 1) := tendsto_E (k := 4) (by norm_num) (by decide)
  have t6 : Tendsto (⇑E₆) atImInfty (𝓝 1) := tendsto_E (k := 6) (by norm_num) (by decide)
  have tF : Tendsto F atImInfty (𝓝 (B ^ 2 - A ^ 3)) := by
    have h1 : Tendsto (fun z => B ^ 2 * E₄ z ^ 3 - A ^ 3 * E₆ z ^ 2) atImInfty
        (𝓝 (B ^ 2 * 1 ^ 3 - A ^ 3 * 1 ^ 2)) :=
      ((t4.pow 3).const_mul _).sub ((t6.pow 2).const_mul _)
    simp only [one_pow, mul_one] at h1
    exact h1.congr fun z => (hF z).symm
  have hc : B ^ 2 - A ^ 3 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  obtain ⟨z, hz⟩ := exists_zero F _ hc tF
  refine ⟨z, ?_⟩
  rw [hF] at hz
  exact sub_eq_zero.1 hz

lemma exists_scale (A B a b : ℂ) (h : A ^ 3 ≠ B ^ 2) (h' : a ^ 3 ≠ b ^ 2)
    (e : B ^ 2 * a ^ 3 = A ^ 3 * b ^ 2) : ∃ μ : ℂ, μ ≠ 0 ∧ μ ^ 4 * a = A ∧ μ ^ 6 * b = B := by
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by
      rintro rfl
      exact h' (by ring)
    have hA : A = 0 := by
      have h0 : A ^ 3 * b ^ 2 = 0 := by rw [← e]; ring
      exact pow_eq_zero_iff (by norm_num) |>.1 ((mul_eq_zero.1 h0).resolve_right (pow_ne_zero 2 hb))
    subst hA
    have hB : B ≠ 0 := by
      rintro rfl
      exact h (by ring)
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (B / b) (by norm_num : 0 < 6)
    refine ⟨μ, ?_, by ring, ?_⟩
    · rintro rfl
      rw [zero_pow (by norm_num)] at hμ
      exact hB ((div_eq_zero_iff.1 hμ.symm).resolve_right hb)
    · rw [hμ, div_mul_cancel₀ B hb]
  · by_cases hb : b = 0
    · subst hb
      have hB : B = 0 := by
        have h0 : B ^ 2 * a ^ 3 = 0 := by rw [e]; ring
        exact pow_eq_zero_iff (by norm_num) |>.1 ((mul_eq_zero.1 h0).resolve_right (pow_ne_zero 3 ha))
      subst hB
      have hA : A ≠ 0 := by
        rintro rfl
        exact h (by ring)
      obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (A / a) (by norm_num : 0 < 4)
      refine ⟨μ, ?_, ?_, by ring⟩
      · rintro rfl
        rw [zero_pow (by norm_num)] at hμ
        exact hA ((div_eq_zero_iff.1 hμ.symm).resolve_right ha)
      · rw [hμ, div_mul_cancel₀ A ha]
    · have hA : A ≠ 0 := by
        rintro rfl
        have h0 : B ^ 2 * a ^ 3 = 0 := by rw [e]; ring
        have hB : B = 0 :=
          pow_eq_zero_iff (by norm_num) |>.1 ((mul_eq_zero.1 h0).resolve_right (pow_ne_zero 3 ha))
        exact h (by rw [hB]; ring)
      have hB : B ≠ 0 := by
        rintro rfl
        have h0 : A ^ 3 * b ^ 2 = 0 := by rw [← e]; ring
        exact hA (pow_eq_zero_iff (by norm_num) |>.1 ((mul_eq_zero.1 h0).resolve_right (pow_ne_zero 2 hb)))
      have hAb : A * b ≠ 0 := mul_ne_zero hA hb
      obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (B * a / (A * b)) (by norm_num : 0 < 2)
      refine ⟨μ, ?_, ?_, ?_⟩
      · rintro rfl
        rw [zero_pow (by norm_num)] at hμ
        exact div_ne_zero (mul_ne_zero hB ha) hAb hμ.symm
      · have h4 : μ ^ 4 = (B * a / (A * b)) ^ 2 := by rw [← hμ]; ring
        rw [h4, div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ hAb)]
        linear_combination e
      · have h6 : μ ^ 6 = (B * a / (A * b)) ^ 3 := by rw [← hμ]; ring
        rw [h6, div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ hAb)]
        linear_combination B * b * e

lemma G_eq (L : PeriodPair) (z : ℍ) (hz : L.ω₁ = L.ω₂ * z) {k : ℕ} (hk : 3 ≤ k) :
    L.G k = (L.ω₂⁻¹) ^ k * (2 * riemannZeta k * E hk z) := by
  have hE : E hk z = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 (k : ℤ) z := rfl
  calc L.G k = ∑' v : Fin 2 → ℤ, (L.ω₂⁻¹) ^ k * EisensteinSeries.eisSummand k v z := by
        unfold PeriodPair.G
        rw [← (L.latticeEquivProd.symm.toEquiv).tsum_eq, ← (finTwoArrowEquiv ℤ).tsum_eq]
        congr 1
        funext v
        simp only [LinearEquiv.coe_toEquiv, PeriodPair.latticeEquiv_symm_apply, finTwoArrowEquiv_apply,
          EisensteinSeries.eisSummand, zpow_natCast]
        have e : (v 0 : ℂ) * L.ω₁ + v 1 * L.ω₂ = L.ω₂ * (v 0 * z + v 1) := by rw [hz]; ring
        show (((v 0 : ℂ) * L.ω₁ + (v 1 : ℂ) * L.ω₂) ^ k)⁻¹ = _
        rw [e, mul_pow, mul_inv, inv_pow]
        congr 1
        try simp [one_div]
    _ = (L.ω₂⁻¹) ^ k * (riemannZeta k * eisensteinSeries (N := 1) 0 (k : ℤ) z) := by
        rw [tsum_mul_left, tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk z]
    _ = _ := by rw [hE]; ring

lemma zeta_six : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have h6 : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
    simp [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
      bernoulli'_four, h5, Nat.choose]
    norm_num
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  rw [show (2 : ℂ) * ((3 : ℕ) : ℂ) = 6 by norm_num, h6] at h
  rw [h]
  norm_num [Nat.factorial]
  ring

lemma g_eq (L : PeriodPair) (z : ℍ) (hz : L.ω₁ = L.ω₂ * z) :
    L.g₂ = 4 / 3 * ((Real.pi * L.ω₂⁻¹) ^ 4 * E₄ z) ∧
      L.g₃ = 8 / 27 * ((Real.pi * L.ω₂⁻¹) ^ 6 * E₆ z) := by
  have h4 := G_eq L z hz (by norm_num : 3 ≤ 4)
  have h6 := G_eq L z hz (by norm_num : 3 ≤ 6)
  have e4 : (E (by norm_num : 3 ≤ 4)) z = E₄ z := rfl
  have e6 : (E (by norm_num : 3 ≤ 6)) z = E₆ z := rfl
  rw [e4] at h4
  rw [e6] at h6
  simp only [Nat.cast_ofNat] at h4 h6
  rw [riemannZeta_four] at h4
  rw [zeta_six] at h6
  unfold PeriodPair.g₂ PeriodPair.g₃
  rw [h4, h6]
  constructor <;> ring

lemma ω₂_ne_zero (L : PeriodPair) : L.ω₂ ≠ 0 := by
  simpa using L.indep.ne_zero 1

lemma im_ne_zero (L : PeriodPair) : (L.ω₁ / L.ω₂).im ≠ 0 := by
  intro h
  have hω := ω₂_ne_zero L
  set r := (L.ω₁ / L.ω₂).re with hr
  have hz : L.ω₁ / L.ω₂ = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [h])
  have h1 : L.ω₁ = (r : ℂ) * L.ω₂ := by rw [← hz]; field_simp
  have h2 := (LinearIndependent.pair_iff.1 L.indep) 1 (-r) (by
    rw [one_smul, Complex.real_smul, h1]
    push_cast
    ring)
  exact one_ne_zero h2.1

def swap (L : PeriodPair) : PeriodPair where
  ω₁ := L.ω₂
  ω₂ := L.ω₁
  indep := LinearIndependent.pair_symm_iff.mp L.indep

lemma swap_G (L : PeriodPair) (k : ℕ) : (swap L).G k = L.G k := by
  unfold PeriodPair.G PeriodPair.lattice
  show ∑' (l : ↥(Submodule.span ℤ {L.ω₂, L.ω₁})), ((l : ℂ) ^ k)⁻¹ = _
  rw [Set.pair_comm L.ω₂ L.ω₁]

lemma disc_of_pos (L : PeriodPair) (h : 0 < (L.ω₁ / L.ω₂).im) : L.g₂ ^ 3 ≠ 27 * L.g₃ ^ 2 := by
  intro hc
  have hω := ω₂_ne_zero L
  set z : ℍ := UpperHalfPlane.mk (L.ω₁ / L.ω₂) h with hzdef
  have hz : L.ω₁ = L.ω₂ * z := by
    rw [hzdef, UpperHalfPlane.coe_mk]
    field_simp
  obtain ⟨e2, e3⟩ := g_eq L z hz
  rw [e2, e3] at hc
  apply E_cube_ne z
  have hπ : ((Real.pi : ℂ) * L.ω₂⁻¹) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (inv_ne_zero hω)
  have h0 : ((Real.pi : ℂ) * L.ω₂⁻¹) ^ 12 * (64 / 27) * (E₄ z ^ 3 - E₆ z ^ 2) = 0 := by
    linear_combination hc
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exfalso
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact pow_ne_zero _ hπ h2
    · norm_num at h2
  · exact sub_eq_zero.1 h1

lemma disc (L : PeriodPair) : L.g₂ ^ 3 ≠ 27 * L.g₃ ^ 2 := by
  rcases lt_or_gt_of_ne (im_ne_zero L) with h | h
  · have hω₁ : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
    have h' : 0 < ((swap L).ω₁ / (swap L).ω₂).im := by
      show 0 < (L.ω₂ / L.ω₁).im
      rw [← inv_div, Complex.inv_im]
      exact div_pos (neg_pos.2 h) (Complex.normSq_pos.2 (div_ne_zero hω₁ (ω₂_ne_zero L)))
    have h2 := disc_of_pos (swap L) h'
    have e2 : (swap L).g₂ = L.g₂ := by simp only [PeriodPair.g₂, swap_G]
    have e3 : (swap L).g₃ = L.g₃ := by simp only [PeriodPair.g₃, swap_G]
    rwa [e2, e3] at h2
  · exact disc_of_pos L h

lemma uniformisation (a b : ℂ) (h : a ^ 3 ≠ 27 * b ^ 2) :
    ∃ L : PeriodPair, L.g₂ = a ∧ L.g₃ = b := by
  have hAB : (3 / 4 * a) ^ 3 ≠ (27 / 8 * b) ^ 2 := by
    intro hc
    apply h
    linear_combination (64 / 27) * hc
  obtain ⟨z, hz⟩ := exists_ratio (3 / 4 * a) (27 / 8 * b) hAB
  obtain ⟨μ, hμ0, hμ4, hμ6⟩ := exists_scale (3 / 4 * a) (27 / 8 * b) (E₄ z) (E₆ z) hAB (E_cube_ne z) hz
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hω : (Real.pi : ℂ) / μ ≠ 0 := div_ne_zero hπ hμ0
  have hzim : 0 < (z : ℂ).im := by simpa using z.im_pos
  have hind : LinearIndependent ℝ ![(Real.pi : ℂ) / μ * z, (Real.pi : ℂ) / μ] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    rw [Complex.real_smul, Complex.real_smul] at hst
    have h1 : ((s : ℂ) * z + t) * ((Real.pi : ℂ) / μ) = 0 := by linear_combination hst
    have h2 : (s : ℂ) * z + t = 0 := (mul_eq_zero.1 h1).resolve_right hω
    have h3 : s * (z : ℂ).im = 0 := by
      have := congrArg Complex.im h2
      simpa using this
    have hs : s = 0 := (mul_eq_zero.1 h3).resolve_right hzim.ne'
    refine ⟨hs, ?_⟩
    rw [hs] at h2
    simpa using h2
  let L : PeriodPair := ⟨(Real.pi : ℂ) / μ * z, (Real.pi : ℂ) / μ, hind⟩
  obtain ⟨e2, e3⟩ := g_eq L z rfl
  have hπω : (Real.pi : ℂ) * L.ω₂⁻¹ = μ := by
    show (Real.pi : ℂ) * ((Real.pi : ℂ) / μ)⁻¹ = μ
    field_simp
  refine ⟨L, ?_, ?_⟩
  · rw [e2, hπω, hμ4]
    ring
  · rw [e3, hπω, hμ6]
    ring

theorem main (σ : ℂ ≃+* ℂ) (L : PeriodPair) :
    ∃ L' : PeriodPair, L'.g₂ = σ L.g₂ ∧ L'.g₃ = σ L.g₃ := by
  apply uniformisation
  intro h
  apply disc L
  apply σ.injective
  simp only [map_pow, map_mul, map_ofNat]
  exact h

end GlobalTheory.DiscUniformisation
