import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep

open MeasureTheory

theorem UpperTheory.TP.absNe :
    UpperTheory.TP.AbsNe := by
  intro A B C _ _ _ μA μB μC _ _ _ H K hH hK hH0 hHtop hKtop f m s c₀ κ r w hκ hr hf hoff hon hm hK1 hbd hlt
  have hG := hf.integral_prod_right
  have hGeq : (fun y : B × C => ∫ x, f (x, y) ∂μA) =
      fun y => H.indicator (fun _ => (1 : ℂ)) y.1 * (κ * (s y.2 * c₀ y.2)) := by
    funext ⟨b, c⟩
    by_cases hb : b ∈ H
    · have e : (fun x => f (x, b, c)) = fun x => s c * m x c := funext fun x => hon x c b hb
      simp only [e, integral_const_mul, hm, Set.indicator_of_mem hb, one_mul]
      ring
    · have e : (fun x => f (x, b, c)) = fun _ => (0 : ℂ) := funext fun x => hoff x b c hb
      simp [e, hb]
  have hv : Integrable (fun c => s c * c₀ c) μC := by
    rw [hGeq] at hG
    have hae := hG.prod_right_ae
    by_contra hni
    have hnot : ∀ᵐ b ∂μB, b ∉ H := by
      filter_upwards [hae] with b hb hbH
      apply hni
      have h1 : Integrable (fun c => κ * (s c * c₀ c)) μC := by simpa [hbH] using hb
      have h2 := h1.const_mul κ⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hκ] using h2
    have h0 := ae_iff.mp hnot
    simp only [not_not, Set.setOf_mem_eq] at h0
    exact hH0 h0
  have hI : ∫ y, f y ∂μA.prod (μB.prod μC) =
      (∫ b, H.indicator (fun _ => (1 : ℂ)) b ∂μB) * (κ * ∫ c, s c * c₀ c ∂μC) := by
    rw [integral_prod_symm _ hf, hGeq,
      integral_prod_mul (fun b => H.indicator (fun _ => (1 : ℂ)) b) (fun c => κ * (s c * c₀ c)),
      integral_const_mul]
  have hind : ∫ b, H.indicator (fun _ => (1 : ℂ)) b ∂μB ≠ 0 := by
    rw [integral_indicator hH, setIntegral_const]
    simp [Measure.real, ENNReal.toReal_eq_zero_iff, hH0, hHtop]
  have hp : ∫ c, s c * c₀ c ∂μC ≠ 0 := by
    intro h0
    have hsplit := integral_add_compl hK hv
    rw [h0] at hsplit
    have hKint : ∫ c in K, s c * c₀ c ∂μC = ∫ c in K, (r : ℂ) ∂μC :=
      setIntegral_congr_fun hK fun c hc => by simp [(hK1 c hc).1, (hK1 c hc).2]
    have eq : ‖∫ c in K, s c * c₀ c ∂μC‖ₑ = ‖∫ c in Kᶜ, s c * c₀ c ∂μC‖ₑ := by
      rw [eq_neg_of_add_eq_zero_left hsplit, enorm_neg]
    have lower : ‖∫ c in K, s c * c₀ c ∂μC‖ₑ = μC K * ENNReal.ofReal r := by
      rw [hKint, setIntegral_const, ← ofReal_norm_eq_enorm]
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr]
      rw [Measure.real, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hKtop]
    have upper : ‖∫ c in Kᶜ, s c * c₀ c ∂μC‖ₑ ≤ (∫⁻ c in Kᶜ, w c ∂μC) * ENNReal.ofReal r := by
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun c => ?_
      rw [enorm_mul]
      refine mul_le_mul' (hbd c).2 ?_
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hbd c).1
    have strict := ENNReal.mul_lt_mul_left (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top hlt
    rw [eq] at lower
    exact absurd (lower ▸ upper) (not_le.mpr strict)
  rw [hI]
  exact mul_ne_zero hind (mul_ne_zero hκ hp)
