import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompact

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal
open GlobalTheory.CxForm GlobalTheory.ChartGlue

namespace GlobalTheory.LineForm.FnMul

section Chart

variable {M : Type} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] {n : ℕ}

theorem lintegral_chartMeas (e : OpenPartialHomeomorph M (V n)) {ρ f : M → ℝ≥0∞} (hf : Measurable f)
    (hρ : AEMeasurable (ρ ∘ e.symm) (volume.restrict e.target)) :
    ∫⁻ y, f y ∂chartMeas e ρ = ∫⁻ v in e.target, f (e.symm v) * ρ (e.symm v) := by
  have h0 : AEMeasurable e.symm (volume.restrict e.target) :=
    e.continuousOn_symm.aemeasurable e.open_target.measurableSet
  have h : AEMeasurable e.symm ((volume.restrict e.target).withDensity (ρ ∘ e.symm)) :=
    h0.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [chartMeas, lintegral_map' hf.aemeasurable h,
    lintegral_withDensity_eq_lintegral_mul₀ hρ (g := fun v => f (e.symm v)) (hf.comp_aemeasurable h0)]
  exact lintegral_congr fun v => mul_comm _ _

theorem ofReal_mul_eq (a b : ℝ) : ENNReal.ofReal (a * b) =
    ENNReal.ofReal a * ENNReal.ofReal b + ENNReal.ofReal (-a) * ENNReal.ofReal (-b) := by
  rcases le_total 0 a with ha | ha
  · rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_of_nonpos (neg_nonpos.2 ha), zero_mul, add_zero]
  · rw [← neg_mul_neg, ENNReal.ofReal_mul (neg_nonneg.2 ha), ENNReal.ofReal_of_nonpos ha, zero_mul, zero_add]

variable [SecondCountableTopology M] (A : HolAtlas M n)

def glue (r : A.ι → V n → ℝ) : Measure M := glueMeas A.e fun i y => ENNReal.ofReal (r i (A.e i y))

theorem setLIntegral_glue {r : A.ι → V n → ℝ} (hr : ∀ i, ContinuousOn (r i) (A.e i).target)
    (hc : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r i (A.e i y) = ‖transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y))
    {f : M → ℝ≥0∞} (hf : Measurable f) (i : A.ι) {S : Set M} (hS : MeasurableSet S) (h : S ⊆ (A.e i).source) :
    ∫⁻ y in S, f y ∂glue A r =
      ∫⁻ v in (A.e i).target, S.indicator f ((A.e i).symm v) * ENNReal.ofReal (r i v) := by
  have h1 : (glue A r).restrict S = (chartMeas (A.e i) fun y => ENNReal.ofReal (r i (A.e i y))).restrict S :=
    (Measure.restrict_congr_meas hS).2 fun t ht htm =>
      glueMeas_apply A.e (fun i y => ENNReal.ofReal (r i (A.e i y))) A.holo (fun i j y hi hj => by
        rw [hc i j y hi hj, ENNReal.ofReal_mul (by positivity)]) i htm (ht.trans h)
  have h2 : ∀ᵐ v ∂volume.restrict (A.e i).target, ENNReal.ofReal (r i v) =
      ENNReal.ofReal (r i (A.e i ((A.e i).symm v))) :=
    (ae_restrict_iff' (A.e i).open_target.measurableSet).2 (.of_forall fun v hv => by rw [(A.e i).right_inv hv])
  rw [h1, ← lintegral_indicator hS, lintegral_chartMeas _ (ρ := fun y => ENNReal.ofReal (r i (A.e i y))) (hf.indicator hS)
    (((ENNReal.continuous_ofReal.comp_continuousOn (hr i)).aemeasurable
      (A.e i).open_target.measurableSet).congr h2)]
  refine lintegral_congr_ae ?_
  filter_upwards [h2] with v hv
  rw [hv]

theorem glue_mul {r : A.ι → V n → ℝ} (hr : ∀ i, ContinuousOn (r i) (A.e i).target)
    (hc : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r i (A.e i y) = ‖transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y))
    {g : M → ℝ} (hg : Continuous g) :
    glue A (fun i v => g ((A.e i).symm v) * r i v) =
      (glue A r).withDensity (fun y => ENNReal.ofReal (g y)) +
        (glue A fun i v => -r i v).withDensity fun y => ENNReal.ofReal (-g y) := by
  refine ext_of_cover (fun i => (A.e i).source) (fun i => (A.e i).open_source) A.cover fun i S hS h => ?_
  have m1 : Measurable fun y => ENNReal.ofReal (g y) := hg.measurable.ennreal_ofReal
  have m2 : Measurable fun y => ENNReal.ofReal (-g y) := hg.neg.measurable.ennreal_ofReal
  have h0 : AEMeasurable (A.e i).symm (volume.restrict (A.e i).target) :=
    (A.e i).continuousOn_symm.aemeasurable (A.e i).open_target.measurableSet
  have e0 := setLIntegral_glue A (r := fun i v => g ((A.e i).symm v) * r i v)
    (fun i => (hg.comp_continuousOn (A.e i).continuousOn_symm).mul (hr i))
    (fun i j y hi hj => by
      simp only [(A.e i).left_inv hi, (A.e j).left_inv hj, hc i j y hi hj]; ring)
    (f := fun _ => 1) measurable_const i hS h
  rw [setLIntegral_one] at e0
  rw [e0, Measure.add_apply, withDensity_apply _ hS, withDensity_apply _ hS,
    setLIntegral_glue A hr hc m1 i hS h,
    setLIntegral_glue A (r := fun i v => -r i v) (fun i => (hr i).neg)
      (fun i j y hi hj => by simp only [hc i j y hi hj]; ring) m2 i hS h,
    ← lintegral_add_left' (f := fun v => S.indicator (fun y => ENNReal.ofReal (g y)) ((A.e i).symm v) *
      ENNReal.ofReal (r i v)) (((m1.indicator hS).comp_aemeasurable h0).mul
      ((ENNReal.continuous_ofReal.comp_continuousOn (hr i)).aemeasurable (A.e i).open_target.measurableSet))]
  refine lintegral_congr fun v => ?_
  by_cases hv : (A.e i).symm v ∈ S
  · simp only [Function.comp_apply, indicator_of_mem hv, one_mul, ofReal_mul_eq]
  · simp only [Function.comp_apply, indicator_of_notMem hv, zero_mul, add_zero]

end Chart

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem dens_loc_fn_mul (g : M → ℝ) (ψ : A.Fld) (i : A.ι) (v : V n) :
    (dens (A.loc (A.fn g * ψ) i v)).re = g ((A.e i).symm v) * (dens (A.loc ψ i v)).re := by
  have key : ∀ x : A.Pt, (dens ((A.fn g * ψ) x)).re = g x.pt * (dens (ψ x)).re := fun x => by
    rw [Pi.mul_apply, HolAtlas.fn, ← Algebra.smul_def, ← Complex.re_ofReal_mul]
    simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]
  unfold HolAtlas.loc
  split_ifs with h
  · exact key _
  · simp [dens]

theorem dens_compat {ψ : A.Fld} (hψ : A.IsForm ψ) (i j : A.ι) (y : M) (hi : y ∈ (A.e i).source)
    (hj : y ∈ (A.e j).source) :
    (dens (A.loc ψ i (A.e i y))).re = ‖transDet (A.e i) (A.e j) y‖ ^ 2 * (dens (A.loc ψ j (A.e j y))).re := by
  have h1 := A.loc_crd ψ (⟨(i, y), hi⟩ : A.Pt)
  have h2 := A.loc_crd ψ (⟨(j, y), hj⟩ : A.Pt)
  have h3 := hψ.compat (⟨(i, y), hi⟩ : A.Pt) ⟨(j, y), hj⟩ rfl
  erw [h1, h2, h3, dens_pull]
  rw [Complex.re_ofReal_mul]
  rfl

end GlobalTheory.LineForm.FnMul

namespace GlobalTheory.LineForm

open GlobalTheory.LineForm.FnMul

theorem integral_fn_mul : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (g : M → ℝ),
    Continuous g → ∀ ψ : A.Fld, A.IsForm ψ → A.integral (A.fn g * ψ) = wInt A g ψ := by
  intro M _ _ _ _ _ _ n A g hg ψ hψ
  set r : A.ι → V n → ℝ := fun i v => (dens (A.loc ψ i v)).re with hr
  have rc : ∀ i, ContinuousOn (r i) (A.e i).target := fun i =>
    Complex.continuous_re.comp_continuousOn ((hψ.smooth i Finset.univ).continuousOn.div_const _)
  have rt := dens_compat A hψ
  have nc : ∀ i, ContinuousOn (fun v => -r i v) (A.e i).target := fun i => (rc i).neg
  have nt : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      -r i (A.e i y) = ‖transDet (A.e i) (A.e j) y‖ ^ 2 * -r j (A.e j y) := fun i j y hi hj => by
    simp only [hr, rt i j y hi hj]; ring
  have p1 : A.part ψ 1 = glue A r := by simp [HolAtlas.part, glue, hr]
  have p2 : A.part ψ (-1) = glue A fun i v => -r i v := by simp [HolAtlas.part, glue, hr]
  have q1 : A.part (A.fn g * ψ) 1 = glue A fun i v => g ((A.e i).symm v) * r i v := by
    simp [HolAtlas.part, glue, hr, dens_loc_fn_mul]
  have q2 : A.part (A.fn g * ψ) (-1) = glue A fun i v => g ((A.e i).symm v) * -r i v := by
    simp [HolAtlas.part, glue, hr, dens_loc_fn_mul]
  have f1 : IsFiniteMeasure (glue A r) :=
    ⟨lt_top_iff_ne_top.2 (glueMeas_univ_ne_top_of_compact A.e A.cover A.holo r rc rt)⟩
  have f2 : IsFiniteMeasure (glue A fun i v => -r i v) :=
    ⟨lt_top_iff_ne_top.2 (glueMeas_univ_ne_top_of_compact A.e A.cover A.holo (fun i v => -r i v) nc nt)⟩
  have i1 : Integrable g (glue A r) := hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  have i2 : Integrable g (glue A fun i v => -r i v) :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  rw [glue_mul A rc rt hg] at q1
  rw [glue_mul A (r := fun i v => -r i v) nc nt hg] at q2
  simp only [neg_neg] at q2
  rw [wInt, HolAtlas.integral, q1, q2, p1, p2, integral_eq_lintegral_pos_part_sub_lintegral_neg_part i1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part i2]
  simp only [Measure.real, Measure.add_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have j1 : ∫⁻ y, ENNReal.ofReal (-g y) ∂glue A r ≠ ∞ := i1.neg.lintegral_lt_top.ne
  have j2 : ∫⁻ y, ENNReal.ofReal (-g y) ∂glue A (fun i v => -r i v) ≠ ∞ := i2.neg.lintegral_lt_top.ne
  rw [ENNReal.toReal_add i1.lintegral_lt_top.ne j2, ENNReal.toReal_add i2.lintegral_lt_top.ne j1]
  ring

end GlobalTheory.LineForm
