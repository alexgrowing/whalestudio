import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open UpperHalfPlane hiding I
open MeasureTheory Complex CongruenceSubgroup Filter Topology Asymptotics
open scoped MatrixGroups ModularForm Modular ENNReal NNReal Pointwise
open ConjAct
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.CuspHeight

theorem volume_strip_lt_top : volume {z : ℍ | |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im} < ⊤ := by
  let Φ := Complex.measurableEquivRealProd
  let s : Set (ℝ × ℝ) := Set.Icc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Set.Ioi (1 / 4 : ℝ)
  let gg : ℝ → ℝ≥0∞ := fun y => ((((1 / ‖y‖₊) ^ 2 : ℝ≥0)) : ℝ≥0∞)
  rw [volume_eq_lintegral]
  have hsub : (UpperHalfPlane.coe '' {z : ℍ | |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im}) ⊆ Φ ⁻¹' s := by
    rintro _ ⟨z, ⟨h1, h2⟩, rfl⟩
    have h3 := abs_le.1 h1
    simp only [Set.mem_preimage, s, Set.mem_prod, Set.mem_Icc, Set.mem_Ioi, Φ,
      Complex.measurableEquivRealProd_apply]
    refine ⟨⟨h3.1, h3.2⟩, ?_⟩
    have : (1 / 2 : ℝ) ≤ (z : ℂ).im := h2
    linarith
  refine (lintegral_mono_set hsub).trans_lt ?_
  have h1 := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Φ.measurableEmbedding (fun p : ℝ × ℝ => gg p.2) s
  have h2 : ∫⁻ a in Φ ⁻¹' s, ((((1 / ‖a.im‖₊) ^ 2 : ℝ≥0)) : ℝ≥0∞) =
      ∫⁻ a in Φ ⁻¹' s, gg (Φ a).2 := rfl
  rw [h2, h1, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have h3 : ∫⁻ p : ℝ × ℝ, gg p.2 ∂((volume.restrict (Set.Icc (-(1 / 2) : ℝ) (1 / 2))).prod
      (volume.restrict (Set.Ioi (1 / 4 : ℝ)))) =
      (∫⁻ _ in Set.Icc (-(1 / 2) : ℝ) (1 / 2), 1) * ∫⁻ y in Set.Ioi (1 / 4 : ℝ), gg y := by
    rw [← lintegral_prod_mul aemeasurable_const (by fun_prop)]
    simp
  rw [h3]
  refine ENNReal.mul_lt_top (by simp) ?_
  have h4 : ∫⁻ y in Set.Ioi (1 / 4 : ℝ), gg y =
      ∫⁻ y in Set.Ioi (1 / 4 : ℝ), ENNReal.ofReal (y ^ (-2 : ℝ)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0 : ℝ) < y := lt_trans (by norm_num) hy
    simp only [gg]
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    rw [Real.rpow_neg hy0.le]
    simp [abs_of_pos hy0]
  rw [h4]
  exact (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).lintegral_lt_top

theorem fd_subset_strip : (𝒟 : Set ℍ) ⊆ {z : ℍ | |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im} := by
  intro z hz
  refine ⟨hz.2, ?_⟩
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  nlinarith [z.im_pos]

theorem volume_fd_lt_top : volume (𝒟 : Set ℍ) < ⊤ :=
  (measure_mono fd_subset_strip).trans_lt volume_strip_lt_top

theorem measurableSet_fd : MeasurableSet (𝒟 : Set ℍ) := by
  have h1 : IsClosed {z : ℍ | 1 ≤ Complex.normSq (z : ℂ)} :=
    isClosed_le continuous_const (Complex.continuous_normSq.comp continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ 1 / 2} :=
    isClosed_le (continuous_abs.comp continuous_re) continuous_const
  exact (h1.inter h2).measurableSet

theorem exists_bound_slash (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic]
    (f : CuspForm Γ k) (σ : SL(2, ℤ)) (m : ℕ) :
    ∃ F : ℝ, ∀ τ ∈ 𝒟, ‖((f : ℍ → ℂ) ∣[k] σ) τ‖ * (1 + τ.im) ^ m ≤ F := by
  have : ((toConjAct (σ : GL (Fin 2) ℝ)⁻¹) • Γ).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv,
      Matrix.SpecialLinearGroup.map_mapGL]
      using! Subgroup.IsArithmetic.conj Γ (Matrix.SpecialLinearGroup.mapGL ℚ σ)⁻¹
  let h := CuspForm.translate f (σ : GL (Fin 2) ℝ)
  obtain ⟨c, hc, hO⟩ := CuspFormClass.exp_decay_atImInfty' h
  have hh : ∀ τ, h τ = ((f : ℍ → ℂ) ∣[k] σ) τ := fun τ => rfl
  have hcont : Continuous fun τ : ℍ => ‖h τ‖ * (1 + τ.im) ^ m := by
    have : Continuous (h : ℍ → ℂ) := (ModularFormClass.holo h).continuous
    exact (this.norm).mul ((continuous_const.add UpperHalfPlane.continuous_im).pow m)
  have h1 : (fun t : ℝ => Real.exp (-c * t) * (1 + t) ^ m) =O[atTop] fun _ => (1 : ℝ) := by
    have h2 := ((isLittleO_pow_exp_pos_mul_atTop m hc).isBigO).comp_tendsto
      (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
    have h3 := (isBigO_refl (fun t : ℝ => Real.exp (-c * t)) atTop).mul h2
    refine h3.trans (IsBigO.of_bound (Real.exp c) (Eventually.of_forall fun t => ?_))
    simp only [Function.comp, id, ← Real.exp_add, norm_one, mul_one]
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact le_of_eq (by congr 1; ring)
  have h4 : (fun τ : ℍ => ‖h τ‖ * (1 + τ.im) ^ m) =O[atImInfty] fun z : ℍ => z.im ^ (0 : ℝ) := by
    have h5 := hO.norm_left.mul (isBigO_refl (fun τ : ℍ => (1 + τ.im) ^ m) atImInfty)
    refine h5.trans ?_
    simp only [Real.rpow_zero]
    exact h1.comp_tendsto (tendsto_comap (f := fun τ : ℍ => τ.im) (x := atTop))
  obtain ⟨F, hF⟩ := ModularGroup.exists_bound_fundamental_domain_of_isBigO hcont h4
  refine ⟨F, fun τ hτ => ?_⟩
  have := hF τ hτ
  simp only [Real.rpow_zero, mul_one] at this
  rw [← hh]
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)

theorem norm_lin_le (p q : ℤ) (τ : ℍ) (h1 : |τ.re| ≤ 1 / 2) (h2 : 0 < τ.im) :
    ‖(p : ℂ) * (τ : ℂ) + q‖ ≤ ((|p| + |q| : ℤ) : ℝ) * (1 + τ.im) := by
  have h3 : ‖(τ : ℂ)‖ ≤ 1 + τ.im := by
    have h4 := Complex.norm_le_abs_re_add_abs_im (τ : ℂ)
    have h5 : |(τ : ℂ).im| = τ.im := abs_of_pos h2
    have h6 : |(τ : ℂ).re| ≤ 1 / 2 := h1
    linarith
  have h7 : ‖(p : ℂ)‖ = |(p : ℝ)| := by simp
  have h8 : ‖(q : ℂ)‖ = |(q : ℝ)| := by simp
  calc ‖(p : ℂ) * (τ : ℂ) + q‖ ≤ ‖(p : ℂ)‖ * ‖(τ : ℂ)‖ + ‖(q : ℂ)‖ :=
        (norm_add_le _ _).trans (by rw [norm_mul])
    _ ≤ |(p : ℝ)| * (1 + τ.im) + |(q : ℝ)| * (1 + τ.im) := by
        rw [h7, h8]
        have : 0 ≤ |(q : ℝ)| := abs_nonneg _
        have := mul_le_mul_of_nonneg_left h3 (abs_nonneg (p : ℝ))
        nlinarith [τ.im_pos]
    _ = _ := by push_cast; ring

theorem Ht_smul (σ : SL(2, ℤ)) (τ : ℍ) :
    Ht (σ • τ) = (‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ^ 2 +
      ‖((σ 0 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 0 1 : ℤ)‖ ^ 2) / τ.im := by
  have hD : ((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ) ≠ 0 := by
    simpa [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero (σ : GL (Fin 2) ℝ) τ
  have hn : ‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ≠ 0 := norm_ne_zero_iff.2 hD
  have him : (σ • τ).im = τ.im / ‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq, ModularGroup.denom_apply]
  have hco : ((σ • τ : ℍ) : ℂ) = (((σ 0 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 0 1 : ℤ)) /
      (((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp
  have key : ∀ a b y : ℝ, a ≠ 0 → y ≠ 0 → (1 + (b / a) ^ 2) / (y / a ^ 2) = (a ^ 2 + b ^ 2) / y := by
    intro a b y ha hy
    field_simp
  unfold Ht
  rw [hco, norm_div, him]
  exact key _ _ _ hn τ.im_ne_zero

theorem exists_height_bound (σ : SL(2, ℤ)) (k A : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ 𝒟,
    ‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ^ k * Ht (σ • τ) ^ A ≤ C * (1 + τ.im) ^ (k + 2 * A) := by
  set P : ℝ := ((|σ 1 0| + |σ 1 1| : ℤ) : ℝ) with hP
  set Q : ℝ := ((|σ 0 0| + |σ 0 1| : ℤ) : ℝ) with hQ
  have hP0 : 0 ≤ P := by rw [hP]; exact_mod_cast (by positivity : 0 ≤ |σ 1 0| + |σ 1 1|)
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact_mod_cast (by positivity : 0 ≤ |σ 0 0| + |σ 0 1|)
  refine ⟨P ^ k * (2 * (P ^ 2 + Q ^ 2)) ^ A, by positivity, fun τ hτ => ?_⟩
  have hs := fd_subset_strip hτ
  have hy : 0 < τ.im := τ.im_pos
  have h1 := norm_lin_le (σ 1 0) (σ 1 1) τ hs.1 hy
  have h2 := norm_lin_le (σ 0 0) (σ 0 1) τ hs.1 hy
  have hu : 0 ≤ 1 + τ.im := by linarith
  have h3 : Ht (σ • τ) ≤ 2 * (P ^ 2 + Q ^ 2) * (1 + τ.im) ^ 2 := by
    rw [Ht_smul, div_le_iff₀ hy]
    have h4 : ‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ^ 2 ≤ (P * (1 + τ.im)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h5 : ‖((σ 0 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 0 1 : ℤ)‖ ^ 2 ≤ (Q * (1 + τ.im)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h6 : 0 ≤ (P ^ 2 + Q ^ 2) * (1 + τ.im) ^ 2 := by positivity
    have h7 : 1 ≤ 2 * τ.im := by linarith [hs.2]
    nlinarith
  have h8 : 0 ≤ Ht (σ • τ) := by
    unfold Ht
    have := (σ • τ).im_pos
    positivity
  calc ‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ^ k * Ht (σ • τ) ^ A
      ≤ (P * (1 + τ.im)) ^ k * (2 * (P ^ 2 + Q ^ 2) * (1 + τ.im) ^ 2) ^ A := by
        gcongr
    _ = _ := by
        rw [mul_pow, mul_pow (2 * (P ^ 2 + Q ^ 2)), ← pow_mul, pow_add]
        ring

theorem continuous_Ht : Continuous Ht := by
  unfold Ht
  refine Continuous.div ?_ UpperHalfPlane.continuous_im fun z => z.im_ne_zero
  exact continuous_const.add (continuous_coe.norm.pow 2)

theorem integrableOn_translate_fd : D1 := by
  intro k N _ f σ A
  let φ : ℍ → ℍ := fun z => σ • z
  have hcf : Continuous (f : ℍ → ℂ) := (ModularFormClass.holo f).continuous
  have hG : Continuous fun z : ℍ => ‖f z‖ * Ht z ^ A := hcf.norm.mul (continuous_Ht.pow A)
  have hφ : Continuous φ := continuous_const_smul (σ : GL (Fin 2) ℝ)
  have hmp : MeasurePreserving φ volume volume :=
    measurePreserving_smul (σ : GL (Fin 2) ℝ) volume
  have hemb : MeasurableEmbedding φ := (MeasurableEquiv.smul (σ : GL (Fin 2) ℝ)).measurableEmbedding
  have hpre : φ ⁻¹' {z | σ⁻¹ • z ∈ 𝒟} = 𝒟 := by
    ext z
    simp [φ, -ModularGroup.sl_moeb]
  rw [← hmp.integrableOn_comp_preimage hemb, hpre]
  obtain ⟨F, hF⟩ := exists_bound_slash (k : ℤ) _ f σ (k + 2 * A)
  obtain ⟨C, hC0, hC⟩ := exists_height_bound σ k A
  refine Measure.integrableOn_of_bounded (M := C * F) volume_fd_lt_top.ne
    (hG.comp hφ).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_fd).2 (Eventually.of_forall fun τ hτ => ?_))
  have hsl : ‖f (σ • τ)‖ = ‖((f : ℍ → ℂ) ∣[(k : ℤ)] σ) τ‖ *
      ‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ^ k := by
    have hD : ‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ≠ 0 := by
      refine norm_ne_zero_iff.2 ?_
      simpa [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero (σ : GL (Fin 2) ℝ) τ
    rw [ModularForm.SL_slash_apply, norm_mul, norm_zpow, ModularGroup.denom_apply]
    simp only [zpow_neg, zpow_natCast]
    field_simp
  have h1 := hC τ hτ
  have h2 := hF τ hτ
  have h8 : 0 ≤ Ht (σ • τ) := by
    unfold Ht
    have := (σ • τ).im_pos
    positivity
  have h9 : 0 ≤ ‖((f : ℍ → ℂ) ∣[(k : ℤ)] σ) τ‖ := norm_nonneg _
  simp only [Function.comp, φ]
  rw [Real.norm_of_nonneg (by positivity), hsl]
  calc ‖((f : ℍ → ℂ) ∣[(k : ℤ)] σ) τ‖ * ‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ^ k * Ht (σ • τ) ^ A
      = ‖((f : ℍ → ℂ) ∣[(k : ℤ)] σ) τ‖ * (‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ^ k * Ht (σ • τ) ^ A) := by
        ring
    _ ≤ ‖((f : ℍ → ℂ) ∣[(k : ℤ)] σ) τ‖ * (C * (1 + τ.im) ^ (k + 2 * A)) := by gcongr
    _ = C * (‖((f : ℍ → ℂ) ∣[(k : ℤ)] σ) τ‖ * (1 + τ.im) ^ (k + 2 * A)) := by ring
    _ ≤ C * F := by gcongr

end GlobalTheory.CompanionTheory.CuspHeight
