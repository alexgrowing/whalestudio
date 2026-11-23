import Mathlib
import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange

open MeasureTheory Filter Topology GlobalTheory.WeilM

noncomputable section
namespace PositivityTheory.ThKEst.W

theorem real_bound (h : CoefReal) (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y] [BorelSpace Y] (β : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hβ : ∀ y, β y = 0 → y = 0) :
    ∃ ν : Measure Y, ν.IsAddHaarMeasure ∧ ∀ N : ℕ, ∃ p : Seminorm ℂ (SchwartzMap Y ℂ), Continuous p ∧
      ∀ (f₁ f₂ : SchwartzMap Y ℂ) (x y : Y), ‖∫ u, Complex.exp (2 * Real.pi * Complex.I * (β y u : ℝ)) * f₁ (u + x) *
        (starRingEnd ℂ) (f₂ u) ∂ν‖ * (1 + ‖x‖ + ‖y‖) ^ N ≤ p f₁ * p f₂ := by
  let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ Y))
  let T : V ≃L[ℝ] Y := (toEuclidean (E := Y)).symm
  refine ⟨Measure.map T volume, T.isAddHaarMeasure_map _, fun N => ?_⟩
  obtain ⟨p, hp, hb⟩ := h V N
  let S : Y →ₗ[ℝ] (V →L[ℝ] ℝ) := (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := ℝ)).toLinearMap ∘ₗ
    (β.compl₂ T.toLinearEquiv.toLinearMap)
  have hS : ∀ y v, S y v = β y (T v) := fun _ _ => rfl
  obtain ⟨K₁, -, hK₁⟩ := S.exists_antilipschitzWith (LinearMap.ker_eq_bot'.2 fun y hy => hβ y (LinearMap.ext fun u => by
    have := hS y (T.symm u)
    rw [hy, T.apply_symm_apply] at this
    exact this.symm))
  let K : NNReal := 1 + K₁ + ‖(T : V →L[ℝ] Y)‖₊
  have hK : (K : ℝ) = 1 + K₁ + ‖(T : V →L[ℝ] Y)‖ := rfl
  let c := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T
  refine ⟨K ^ N • p.comp c.toLinearMap, (hp.comp c.continuous).const_smul (K ^ N), fun f₁ f₂ x y => ?_⟩
  have h1 := hb (c f₁) (c f₂) (T.symm x) ((InnerProductSpace.toDual ℝ V).symm (S y))
  have e : ∫ u, Complex.exp (2 * Real.pi * Complex.I * (β y u : ℝ)) * f₁ (u + x) * (starRingEnd ℂ) (f₂ u)
      ∂(Measure.map T volume) = ∫ u, Complex.exp (2 * Real.pi * Complex.I *
        (inner ℝ u ((InnerProductSpace.toDual ℝ V).symm (S y)) : ℝ)) * c f₁ (u + T.symm x) * (starRingEnd ℂ) (c f₂ u) := by
    rw [show Measure.map T volume = Measure.map T.toHomeomorph.toMeasurableEquiv volume from rfl, integral_map_equiv]
    refine integral_congr_ae (.of_forall fun u => ?_)
    simp only [real_inner_comm _ u, InnerProductSpace.toDual_symm_apply, hS]
    simp [c]
  rw [e]
  rw [LinearIsometryEquiv.norm_map] at h1
  have hx : ‖x‖ ≤ ‖(T : V →L[ℝ] Y)‖ * ‖T.symm x‖ := by simpa using (T : V →L[ℝ] Y).le_opNorm (T.symm x)
  have hy : ‖y‖ ≤ K₁ * ‖S y‖ := by
    have := hK₁.le_mul_dist y 0
    rwa [map_zero, dist_eq_norm, dist_eq_norm, sub_zero, sub_zero] at this
  have n1 := norm_nonneg (T : V →L[ℝ] Y)
  have n2 := norm_nonneg (T.symm x)
  have n3 := norm_nonneg (S y)
  have n4 := K₁.coe_nonneg
  have h2 : 1 + ‖x‖ + ‖y‖ ≤ K * (1 + ‖T.symm x‖ + ‖S y‖) := by
    rw [hK]
    nlinarith [mul_nonneg n1 n3, mul_nonneg n4 n2]
  have hK1 : (1 : ℝ) ≤ K ^ N := one_le_pow₀ (by rw [hK]; linarith)
  have q := mul_nonneg (apply_nonneg p (c f₁)) (apply_nonneg p (c f₂))
  calc _ ≤ _ * (K * (1 + ‖T.symm x‖ + ‖S y‖)) ^ N := by gcongr
    _ = K ^ N * (_ * (1 + ‖T.symm x‖ + ‖S y‖) ^ N) := by rw [mul_pow, mul_left_comm]
    _ ≤ K ^ N * (p (c f₁) * p (c f₂)) := by gcongr
    _ ≤ K ^ N * (K ^ N * (p (c f₁) * p (c f₂))) := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left q hK1) (zero_le_one.trans hK1)
    _ = _ := by
      simp only [Seminorm.smul_apply, Seminorm.comp_apply, NNReal.smul_def, NNReal.coe_pow, smul_eq_mul,
        ContinuousLinearMap.coe_coe]
      ring

theorem sb_inv {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] {φ : G → ℂ} (hφ : φ ∈ SB G) :
    ∀ᶠ k in 𝓝 (0 : G), ∀ x, φ (x + k) = φ x := by
  have h1 : ∀ᶠ k in 𝓝 (0 : G), ∀ x ∈ tsupport φ, φ (x + k) = φ x ∧ φ (x - k) = φ x :=
    hφ.2.isCompact.eventually_forall_of_forall_eventually fun x _ => by
      have a := (hφ.1.comp_continuous (f := fun z : G × G => z.2 + z.1) (by fun_prop)).eventually_eq (0, x)
      have b := (hφ.1.comp_continuous (f := fun z : G × G => z.2 - z.1) (by fun_prop)).eventually_eq (0, x)
      have c := (hφ.1.comp_continuous (f := fun z : G × G => z.2) (by fun_prop)).eventually_eq (0, x)
      filter_upwards [a, b, c] with z a b c
      simp only [Function.comp, add_zero, sub_zero] at a b c
      exact ⟨a.trans c.symm, b.trans c.symm⟩
  filter_upwards [h1] with k hk x
  by_cases hx : x ∈ tsupport φ
  · exact (hk x hx).1
  by_cases hx' : x + k ∈ tsupport φ
  · simpa using (hk _ hx').2.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem fin_bound {G H : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G] [TopologicalSpace H] (ν : Measure G) [ν.IsAddHaarMeasure] (χ : H → G → ℂ) (hn : ∀ y u, ‖χ y u‖ = 1)
    (ha : ∀ y u u', χ y (u + u') = χ y u * χ y u')
    (hd : ∀ U ∈ 𝓝 (0 : G), ∃ K, IsCompact K ∧ ∀ y, (∀ u ∈ U, χ y u = 1) → y ∈ K) {φ₁ φ₂ : G → ℂ} (h₁ : φ₁ ∈ SB G)
    (h₂ : φ₂ ∈ SB G) : ∃ (C : ℝ) (K : Set (G × H)), IsCompact K ∧ ∀ x y,
      ‖∫ u, χ y u * φ₁ (u + x) * (starRingEnd ℂ) (φ₂ u) ∂ν‖ ≤ C ∧
      (∫ u, χ y u * φ₁ (u + x) * (starRingEnd ℂ) (φ₂ u) ∂ν ≠ 0 → (x, y) ∈ K) := by
  obtain ⟨C, hC⟩ := h₁.1.continuous.bounded_above_of_compact_support h₁.2
  obtain ⟨K, hK, hK'⟩ := hd _ ((sb_inv h₁).and (sb_inv h₂))
  have hi : Integrable φ₂ ν := h₂.1.continuous.integrable_of_hasCompactSupport h₂.2
  refine ⟨∫ u, C * ‖φ₂ u‖ ∂ν, ((fun z : G × G => z.1 - z.2) '' (tsupport φ₁ ×ˢ tsupport φ₂)) ×ˢ K,
    ((h₁.2.isCompact.prod h₂.2.isCompact).image (by fun_prop)).prod hK, fun x y => ⟨?_, fun h0 => ⟨?_, hK' y fun k hk => ?_⟩⟩⟩
  · refine norm_integral_le_of_norm_le (hi.norm.const_mul C) (.of_forall fun u => ?_)
    rw [norm_mul, norm_mul, hn, one_mul, RCLike.norm_conj]
    gcongr
    exact hC _
  · by_contra hx
    refine h0 (integral_eq_zero_of_ae (.of_forall fun u => ?_))
    by_contra hu
    simp only [Pi.zero_apply, mul_eq_zero, not_or, map_eq_zero] at hu
    exact hx ⟨(u + x, u), ⟨subset_tsupport _ hu.1.2, subset_tsupport _ hu.2⟩, add_sub_cancel_left _ _⟩
  · refine (mul_eq_right₀ h0).1 ?_
    rw [← integral_const_mul]
    conv_rhs => rw [← integral_add_right_eq_self _ k]
    refine integral_congr_ae (.of_forall fun u => ?_)
    simp only
    rw [ha, add_right_comm, hk.1, hk.2]
    ring

end PositivityTheory.ThKEst.W
end
