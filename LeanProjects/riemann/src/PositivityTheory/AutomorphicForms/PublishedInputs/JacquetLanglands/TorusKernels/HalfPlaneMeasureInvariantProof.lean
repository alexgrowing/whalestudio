import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace UpperTheory.Esk.HalfPlaneMeasureLemmas

open UpperTheory.Esk

def U : Set ℂ := {z | z.im ≠ 0}

theorem isOpen_U : IsOpen U := isOpen_ne_fun Complex.continuous_im continuous_const

def val (z : P) : ℂ := z.1

def mk (z : ℂ) (hz : z.im ≠ 0) : P := ⟨z, hz⟩

theorem openEmb : Topology.IsOpenEmbedding val :=
  isOpen_U.isOpenEmbedding_subtypeVal

theorem measEmb : MeasurableEmbedding val :=
  openEmb.measurableEmbedding

def rho (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (1 / z.im ^ 2)

def F (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := num g z / den g z

def D (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ ((g.val.det : ℂ) / den g z ^ 2)).restrictScalars ℝ

theorem hasDerivAt_F (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (F g) ((g.val.det : ℂ) / den g z ^ 2) z := by
  have h := ((hasDerivAt_id z).const_mul ((g 0 0 : ℝ) : ℂ) |>.add_const ((g 0 1 : ℝ) : ℂ)).div
    ((hasDerivAt_id z).const_mul ((g 1 0 : ℝ) : ℂ) |>.add_const ((g 1 1 : ℝ) : ℂ)) (den_ne g hz)
  refine h.congr_deriv ?_
  simp only [den, id, mul_one]
  rw [det_eq]
  push_cast
  ring

theorem hasFDerivAt_F (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) : HasFDerivAt (F g) (D g z) z := by
  have := (hasDerivAt_F g hz).hasFDerivAt.restrictScalars ℝ
  simpa [D] using this

theorem det_D (g : GL (Fin 2) ℝ) (z : ℂ) :
    (D g z).det = Complex.normSq ((g.val.det : ℂ) / den g z ^ 2) := by
  simp [D, ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]

theorem F_eq (g : GL (Fin 2) ℝ) (z : P) : F g (val z) = val (g • z) := rfl

theorem injOn_F (g : GL (Fin 2) ℝ) : Set.InjOn (F g) U := by
  intro x hx y hy hxy
  have h : g • mk x hx = g • mk y hy := Subtype.ext hxy
  have := congrArg val (smul_left_cancel g h)
  exact this

theorem key (g : GL (Fin 2) ℝ) {S : Set ℂ} (hS : MeasurableSet S) (hSU : S ⊆ U) :
    ∫⁻ x in F g '' S, rho x = ∫⁻ x in S, rho x := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun x hx => (hasFDerivAt_F g (hSU hx)).hasFDerivWithinAt) ((injOn_F g).mono hSU)]
  refine setLIntegral_congr_fun hS (fun x hx => ?_)
  have hx' : x.im ≠ 0 := hSU hx
  have hd := den_ne g hx'
  have hn : Complex.normSq (den g x) ≠ 0 := by simpa using hd
  have hdet := g.det_ne_zero
  rw [det_D, rho, rho, F, im_div, abs_of_nonneg (Complex.normSq_nonneg _), ← ENNReal.ofReal_mul
    (Complex.normSq_nonneg _)]
  congr 1
  rw [Complex.normSq_div, Complex.normSq_ofReal, map_pow]
  field_simp

theorem vol_def : (volume : Measure P) = (Measure.comap val volume).withDensity fun z => rho (val z) := rfl

theorem vol_eq (s : Set P) (hs : MeasurableSet s) : volume s = ∫⁻ z in val '' s, rho z := by
  rw [vol_def, withDensity_apply _ hs, measEmb.restrict_comap,
← measEmb.lintegral_map, measEmb.map_comap,
    Measure.restrict_restrict (measEmb.measurableSet_range),
    Set.inter_eq_right.2 (Set.image_subset_range _ _)]

theorem image_pre (g : GL (Fin 2) ℝ) (s : Set P) :
    val '' ((fun z : P => g • z) ⁻¹' s) = F g⁻¹ '' (val '' s) := by
  ext x
  simp only [Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨val (g • p), ⟨g • p, hp, rfl⟩, ?_⟩
    rw [F_eq g⁻¹ (g • p), inv_smul_smul]
  · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨g⁻¹ • q, by rwa [smul_inv_smul], ?_⟩
    rw [F_eq]

theorem cont (g : GL (Fin 2) ℝ) : Continuous (fun z : P => g • z) := by
  have hv : Continuous (fun z : P => z.1) := continuous_subtype_val
  have h : Continuous (fun z : P => (g • z).1) := by
    change Continuous (fun z : P => num g z.1 / den g z.1)
    refine Continuous.div ?_ ?_ (fun z => den_ne g z.2)
    · simp only [num]; fun_prop
    · simp only [den]; fun_prop
  exact continuous_induced_rng.2 h

theorem meas_rho : Measurable (fun z : P => rho (val z)) :=
  ENNReal.measurable_ofReal.comp (measurable_const.div ((Complex.measurable_im.comp measEmb.measurable).pow_const 2))

end UpperTheory.Esk.HalfPlaneMeasureLemmas

namespace UpperTheory.Esk

open HalfPlaneMeasureLemmas in
theorem half_plane_measure_invariant_proof : B1a := by
  have : LocallyCompactSpace P := openEmb.locallyCompactSpace
  have : IsFiniteMeasureOnCompacts (Measure.comap val volume) := .comap' _ openEmb.continuous measEmb
  have : SigmaFinite (Measure.comap val volume) := inferInstance
  refine ⟨?_, ?_, fun g => ⟨cont g, ?_⟩⟩
  · rw [vol_def]
    exact SigmaFinite.withDensity_ofReal _
  · have : (Measure.comap val volume).IsOpenPosMeasure := Measure.IsOpenPosMeasure.comap _ openEmb
    refine ⟨fun A hA hne => ?_⟩
    rw [vol_def, Ne, withDensity_apply_eq_zero meas_rho]
    have : {x : P | rho (val x) ≠ 0} ∩ A = A := by
      refine Set.inter_eq_right.2 (fun x _ => ?_)
      have := x.2
      simp only [Set.mem_ofPred_eq, rho, val, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    rw [this]
    exact hA.measure_ne_zero _ hne
  · refine ⟨(cont g).measurable, Measure.ext fun s hs => ?_⟩
    rw [Measure.map_apply (cont g).measurable hs, vol_eq _ ((cont g).measurable hs), vol_eq _ hs,
      image_pre, key _ (measEmb.measurableSet_image.2 hs)]
    rintro _ ⟨p, -, rfl⟩
    exact p.2

end UpperTheory.Esk
