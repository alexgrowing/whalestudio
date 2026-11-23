import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open MeasureTheory Set UpperHalfPlane

private lemma half_le_im {z : ℍ} (hz : z ∈ ModularGroup.fd) : 1 / 2 ≤ z.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have := z.im_pos
  nlinarith

private lemma intOn_of_bdd (hF : UpperTheory.V.Af.Rs.FdFin) (φ : ℍ → ℝ) (hc : Continuous φ) (B : ℝ)
    (hB : ∀ z ∈ ModularGroup.fd, ‖φ z‖ ≤ B) : IntegrableOn φ ModularGroup.fd :=
  Measure.integrableOn_of_bounded hF.2.ne hc.aestronglyMeasurable
    ((ae_restrict_iff' hF.1).2 (Filter.Eventually.of_forall hB))

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.tTop :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.FdPos → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZDiff → UpperTheory.V.Af.Rs.ZLow → UpperTheory.V.Af.Rs.ZInt → UpperTheory.V.Af.Rs.TTop := by
  intro hfd hpos hw hzd hzl hzi L _ G hG hre hex M
  obtain ⟨hGc, C', hC'⟩ := hG
  obtain ⟨C, hC⟩ := hzd L
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (Fintype.card (Fin 2 → ZMod L) : ℝ) := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hNpos : 0 < N := by linarith
  have hcard : ∀ x : ℝ, (Finset.univ : Finset (Fin 2 → ZMod L)).card • x = N * x := by
    intro x
    rw [Finset.card_univ, nsmul_eq_mul, hN]
  obtain ⟨φ, hφ⟩ : ∃ φ : ℍ → ℝ,
      φ = fun z => (∑ v, (G v z).re) / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4) := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℍ → ℝ, ψ = fun z => ∑ v, (G v z).re * z.im ^ 3 := ⟨_, rfl⟩
  have hreC : ∀ v, Continuous fun z => (G v z).re := fun v => Complex.continuous_re.comp (hGc v)
  have himC : Continuous fun z : ℍ => z.im := UpperHalfPlane.continuous_im
  have hnC : Continuous fun z : ℍ => ‖(z : ℂ)‖ := continuous_norm.comp UpperHalfPlane.continuous_coe
  have hden : ∀ z : ℍ, 0 < 2 * N * (‖(z : ℂ)‖ + 1) ^ 4 := fun z => by positivity
  have hφC : Continuous φ := by
    rw [hφ]
    exact (continuous_finset_sum _ (fun v _ => hreC v)).div
      (continuous_const.mul ((hnC.add continuous_const).pow 4)) (fun z => (hden z).ne')
  have hψC : Continuous ψ := by
    rw [hψ]
    exact continuous_finset_sum _ (fun v _ => (hreC v).mul (himC.pow 3))
  have hGb : ∀ v, ∀ z ∈ ModularGroup.fd,
      0 ≤ (G v z).re * z.im ^ 3 ∧ (G v z).re * z.im ^ 3 ≤ C' := by
    intro v z hz
    have hp : 0 ≤ z.im ^ 3 := by
      have := z.im_pos
      positivity
    refine ⟨mul_nonneg (hre v z) hp, ?_⟩
    exact (mul_le_mul_of_nonneg_right (Complex.re_le_norm _) hp).trans (hC' v z (half_le_im hz))
  have hψb : ∀ z ∈ ModularGroup.fd, ‖ψ z‖ ≤ N * C' := by
    intro z hz
    rw [hψ, Real.norm_of_nonneg (Finset.sum_nonneg (fun v _ => (hGb v z hz).1))]
    exact (Finset.sum_le_card_nsmul _ _ _ (fun v _ => (hGb v z hz).2)).trans_eq (hcard _)
  have hφb : ∀ z ∈ ModularGroup.fd, ‖φ z‖ ≤ N * (8 * C') := by
    intro z hz
    have hs0 : 0 ≤ ∑ v, (G v z).re := Finset.sum_nonneg (fun v _ => hre v z)
    have h1 : 1 ≤ 2 * N * (‖(z : ℂ)‖ + 1) ^ 4 := by
      have : 1 ≤ (‖(z : ℂ)‖ + 1) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg (z : ℂ)])
      nlinarith
    rw [hφ, Real.norm_of_nonneg (div_nonneg hs0 (hden z).le)]
    refine (div_le_self hs0 h1).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ (fun v _ => ?_)).trans_eq (hcard _)
    have h8 := (hGb v z hz).2
    have h3 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 2) (half_le_im hz) 3) (hre v z)
    norm_num at h3
    linarith
  have hφI := intOn_of_bdd hfd φ hφC _ hφb
  have hψI := intOn_of_bdd hfd ψ hψC _ hψb
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => by
    rw [hφ]
    exact div_nonneg (Finset.sum_nonneg (fun v _ => hre v z)) (hden z).le
  obtain ⟨v0, z0, hz0, hv0⟩ := hex
  have hc : 0 < ∫ z in ModularGroup.fd, φ z := by
    refine hpos φ hφC hφ0 hφI z0 hz0 ?_
    rw [hφ]
    refine div_pos ?_ (hden z0)
    exact lt_of_lt_of_le hv0
      (Finset.single_le_sum (f := fun v => (G v z0).re) (fun v _ => hre v z0) (Finset.mem_univ v0))
  obtain ⟨c, hcd⟩ : ∃ c, c = ∫ z in ModularGroup.fd, φ z := ⟨_, rfl⟩
  rw [← hcd] at hc
  have hψint : ∫ z in ModularGroup.fd, ψ z ≤ N * C' * volume.real ModularGroup.fd :=
    (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const hfd.2 hψb)
  obtain ⟨s, hs, hWs⟩ := hw.2 ((M + |C| * (N * C' * volume.real ModularGroup.fd)) / c)
  refine ⟨s, hs, ?_⟩
  have hpt : ∀ z ∈ ModularGroup.fd,
      Wsum s * φ z - |C| * ψ z ≤ (∑ v, G v z * (Zc L v s z : ℂ)).re := by
    intro z hz
    have hlow := hzl L s hs z hz
    have hp3 : 0 ≤ z.im ^ 3 := by
      have := z.im_pos
      positivity
    have hZ : ∀ v, Wsum s / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4) - |C| * z.im ^ 3 ≤ Zc L v s z := by
      intro v
      have hsum : ∑ v', Zc L v' s z ≤ N * (Zc L v s z + |C| * z.im ^ 3) := by
        refine (Finset.sum_le_card_nsmul _ _ _ (fun v' _ => ?_)).trans_eq (hcard _)
        have h1 := hC v v' s hs z hz
        have h2 := mul_le_mul_of_nonneg_right (le_abs_self C) hp3
        have h3 := neg_abs_le (Zc L v s z - Zc L v' s z)
        linarith
      have hq : 1 / 2 / (‖(z : ℂ)‖ + 1) ^ 4 * Wsum s =
          N * (Wsum s / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4)) := by
        have := hden z
        field_simp
      have h4 : N * (Wsum s / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4)) ≤ N * (Zc L v s z + |C| * z.im ^ 3) :=
        hq ▸ hlow.trans hsum
      have h5 := le_of_mul_le_mul_left h4 hNpos
      linarith
    rw [Complex.re_sum]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hφ, hψ]
    simp only
    rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum (fun v _ => ?_)
    have h6 := mul_le_mul_of_nonneg_left (hZ v) (hre v z)
    calc Wsum s * ((G v z).re / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4)) - |C| * ((G v z).re * z.im ^ 3)
        = (G v z).re * (Wsum s / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4) - |C| * z.im ^ 3) := by ring
      _ ≤ (G v z).re * Zc L v s z := h6
  have hfI : IntegrableOn (fun z => ∑ v, G v z * (Zc L v s z : ℂ)) ModularGroup.fd :=
    integrable_finset_sum _ (fun v _ => hzi L G ⟨hGc, C', hC'⟩ s hs v v)
  have hre_eq : (∫ z in ModularGroup.fd, ∑ v, G v z * (Zc L v s z : ℂ)).re =
      ∫ z in ModularGroup.fd, (∑ v, G v z * (Zc L v s z : ℂ)).re := (integral_re hfI).symm
  unfold TT
  rw [hre_eq]
  calc M ≤ Wsum s * c - |C| * (N * C' * volume.real ModularGroup.fd) := by
        have := (div_le_iff₀ hc).1 hWs
        linarith
    _ ≤ ∫ z in ModularGroup.fd, (Wsum s * φ z - |C| * ψ z) := by
        rw [integral_sub (hφI.const_mul _) (hψI.const_mul _), integral_const_mul,
          integral_const_mul, ← hcd]
        have := mul_le_mul_of_nonneg_left hψint (abs_nonneg C)
        linarith
    _ ≤ ∫ z in ModularGroup.fd, (∑ v, G v z * (Zc L v s z : ℂ)).re :=
        setIntegral_mono_on ((hφI.const_mul _).sub (hψI.const_mul _)) hfI.re hfd.1 hpt
