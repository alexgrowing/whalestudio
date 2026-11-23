import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcB
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

universe u

theorem fc_det_real (n : ℕ) (J : V n →L[ℂ] V n) :
    |(J.restrictScalars ℝ).det| = ‖J.det‖ ^ 2 := by
  have h : (J.restrictScalars ℝ).det = Complex.normSq J.det := by
    show LinearMap.det ((J : V n →ₗ[ℂ] V n).restrictScalars ℝ) = _
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  rw [h, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]

theorem fc_rho_eq {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) {y : Y}
    (hy : y ∈ A.Mset w0 s De) (i : ι) (hi : y ∈ (A.chart i).source) :
    Real.exp (A.ph A.kap (A.pick y) y) /
        ‖(fderiv ℂ (A.zLoc w0 s (A.pick y)) (A.chart (A.pick y) y)).det‖ ^ 2 =
      Real.exp (A.ph A.kap i y) / ‖(fderiv ℂ (A.zLoc w0 s i) (A.chart i y)).det‖ ^ 2 := by
  have hp := A.mem_pick y
  have hg : 0 < ‖A.g A.kap (A.pick y) i y‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (A.g_ne A.kap (A.pick y) i y hp hi)) 2
  rw [fc_det_jz A hD hy (A.pick y) i hp hi, A.ph_trans A.kap (A.pick y) i y hp hi, Real.exp_sub,
    Real.exp_log hg, norm_mul, mul_pow]
  ring

theorem fc_rho_continuous {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s)
    (hF : A.Flat w0 s De) : Continuous (fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) := by
  rw [continuous_iff_continuousAt]
  intro x0
  have hi0 : (x0 : Y) ∈ (A.chart (A.pick x0)).source := A.mem_pick _
  have hev : (fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) /
      ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) =ᶠ[𝓝 x0]
      fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x0) x) /
        ‖(fderiv ℂ (A.zLoc w0 s (A.pick x0)) (A.chart (A.pick x0) x)).det‖ ^ 2 := by
    have hU : ∀ᶠ x : A.Mset w0 s De in 𝓝 x0, (x : Y) ∈ (A.chart (A.pick x0)).source :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        ((A.chart (A.pick x0)).open_source.mem_nhds hi0)
    filter_upwards [hU] with x hx
    exact fc_rho_eq A hD x.2 (A.pick x0) hx
  refine ContinuousAt.congr ?_ hev.symm
  set i := A.pick (x0 : Y) with hidef
  have hph : ContinuousAt (fun y => A.ph A.kap i y) (x0 : Y) := by
    have h1 : ContinuousAt (A.ph A.kap i ∘ (A.chart i).symm) (A.chart i x0) :=
      ((A.smooth_ph A.kap i).continuousOn).continuousAt
        ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hi0))
    have h2 := h1.comp_of_eq ((A.chart i).continuousAt hi0) rfl
    refine h2.congr ?_
    filter_upwards [(A.chart i).open_source.mem_nhds hi0] with y hy
    simp only [Function.comp_apply, (A.chart i).left_inv hy]
  have hO := fc_isOpen_O A (De := De) hD i
  have hmO := fc_mem_O A x0 i hi0
  have hdetc : ContinuousAt (fun y => (fderiv ℂ (A.zLoc w0 s i) (A.chart i y)).det) (x0 : Y) := by
    have h1 : ContinuousAt (fderiv ℂ (A.zLoc w0 s i)) (A.chart i x0) :=
      ((fc_zLoc_contDiffOn A hD i).continuousOn_fderiv_of_isOpen hO (by simp)).continuousAt
        (hO.mem_nhds hmO)
    exact ContinuousLinearMap.continuous_det.continuousAt.comp
      (h1.comp_of_eq ((A.chart i).continuousAt hi0) rfl)
  have hne := fc_jz_det_ne A hD hF x0.2 i hi0
  have hFc : ContinuousAt (fun y => Real.exp (A.ph A.kap i y) /
      ‖(fderiv ℂ (A.zLoc w0 s i) (A.chart i y)).det‖ ^ 2) (x0 : Y) :=
    (Real.continuous_exp.continuousAt.comp hph).div ((continuous_norm.continuousAt.comp hdetc).pow 2)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
  exact hFc.comp continuous_subtype_val.continuousAt

theorem fc_mu_piece {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s)
    (hF : A.Flat w0 s De) (e : OpenPartialHomeomorph (A.Mset w0 s De) (V n))
    (he : IsChart n (flatStein A hD hF).z e) (i : ι) (B : Set (A.Mset w0 s De))
    (hB : MeasurableSet B) (hBs : B ⊆ e.source) (hBi : ∀ m ∈ B, (m : Y) ∈ (A.chart i).source) :
    A.mu.comap Subtype.val B =
      ∫⁻ m in B, ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) m) ∂vol n (flatStein A hD hF).z := by
  have hMm : MeasurableSet (A.Mset w0 s De) := (isOpen_Mset A hD).measurableSet
  have hemb := MeasurableEmbedding.subtype_coe hMm
  have hz := (flatStein A hD hF).isLocalHomeomorph
  have hρ : Measurable fun m => ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) m) :=
    ENNReal.measurable_ofReal.comp (fc_rho_continuous A hD hF).measurable
  rw [hemb.comap_apply]
  have hBY : MeasurableSet (Subtype.val '' B : Set Y) := hemb.measurableSet_image.2 hB
  rw [A.mu_chart i _ hBY (by rintro _ ⟨m, hm, rfl⟩; exact hBi m hm)]
  have hBimg : MeasurableSet (e '' B) := by
    have := measurableSet_image_of_chart n (flatStein A hD hF).z e he B hB hBs
    rwa [Set.image_congr fun m hm => he (hBs hm)] at this
  have hR : ∫⁻ m in B, ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) m) ∂vol n (flatStein A hD hF).z =
      ∫⁻ w in e '' B, ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) (e.symm w)) := by
    rw [← lintegral_indicator hB, lintegral_vol_chart n _ hz e he _ (hρ.indicator hB)
      (fun m hm => Set.indicator_of_notMem (fun h => hm (hBs h)) _)]
    have hsub : e '' B ⊆ e.target := fun _ ⟨m, hm, hmw⟩ => hmw ▸ e.map_source (hBs hm)
    rw [← Set.inter_eq_left.2 hsub, ← Measure.restrict_restrict hBimg, ← lintegral_indicator hBimg]
    refine setLIntegral_congr_fun e.open_target.measurableSet fun w hw => ?_
    by_cases h : e.symm w ∈ B
    · have hw' : w ∈ e '' B := ⟨e.symm w, h, e.right_inv hw⟩
      simp only [Set.indicator_of_mem h, Set.indicator_of_mem hw']
    · have hw' : w ∉ e '' B := by
        rintro ⟨m, hm, rfl⟩
        exact h (by rw [e.left_inv (hBs hm)]; exact hm)
      simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem hw']
  set S := A.chart i '' (Subtype.val '' B)
  have hS : MeasurableSet S :=
    measurableSet_image_of_chart n (A.chart i) (A.chart i) (fun _ _ => rfl) _ hBY
      (by rintro _ ⟨m, hm, rfl⟩; exact hBi m hm)
  have hSO : S ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De := by
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact fc_mem_O A m i (hBi m hm)
  have hFm : ∀ m ∈ B, A.zLoc w0 s i (A.chart i m) = e m := fun m hm =>
    fc_zLoc_chart A hD e he m (hBs hm) i (hBi m hm)
  have himg : e '' B = A.zLoc w0 s i '' S := by
    rw [Set.image_image, Set.image_image]
    exact (Set.image_congr fun m hm => hFm m hm).symm
  have hinj : Set.InjOn (A.zLoc w0 s i) S := by
    rintro _ ⟨_, ⟨m1, hm1, rfl⟩, rfl⟩ _ ⟨_, ⟨m2, hm2, rfl⟩, rfl⟩ h
    rw [hFm m1 hm1, hFm m2 hm2] at h
    rw [e.injOn (hBs hm1) (hBs hm2) h]
  have hder : ∀ v ∈ S, HasFDerivWithinAt (A.zLoc w0 s i)
      ((fderiv ℂ (A.zLoc w0 s i) v).restrictScalars ℝ) S v := fun v hv =>
    ((((fc_zLoc_contDiffOn A hD i).differentiableOn (by simp)).differentiableAt
      ((fc_isOpen_O A hD i).mem_nhds (hSO hv))).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [hR, himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hder hinj]
  refine setLIntegral_congr_fun hS ?_
  rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
  have hne := fc_jz_det_ne A hD hF m.2 i (hBi m hm)
  simp only
  rw [hFm m hm, e.left_inv (hBs hm), (A.chart i).left_inv (hBi m hm),
    fc_rho_eq A hD m.2 i (hBi m hm), ← ENNReal.ofReal_mul (abs_nonneg _), fc_det_real]
  congr 1
  field_simp

end

end ReciprocityTheory.L2DbarEstimates.Y
