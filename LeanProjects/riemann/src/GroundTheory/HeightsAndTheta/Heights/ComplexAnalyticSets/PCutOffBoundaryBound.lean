import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffBoundaryBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffBoundaryParts
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOff
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffGradient
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace CutOffBoundaryBound

variable {n d : ℕ}

theorem analyticAt_of_isSheetAt {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) : AnalyticAt ℂ s (A *ᵥ x) := by
  obtain ⟨U, hU, hxU, hd, -⟩ := hs
  refine analyticAt_pi_iff.2 fun j => ?_
  have hdj : DifferentiableOn ℂ (fun y => s y j) U := fun y hy =>
    (differentiableAt_pi.1 ((hd y hy).differentiableAt (hU.mem_nhds hy)) j).differentiableWithinAt
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hdj.continuousOn
    (fun z hz i => ?_) _ hxU
  have hu : Function.update z i (z i) = z := Function.update_eq_self i z
  have hdz : DifferentiableAt ℂ (fun y => s y j) (Function.update z i (z i)) := by
    rw [hu]; exact hdj.differentiableAt (hU.mem_nhds hz)
  exact hdz.comp (z i) (hasFDerivAt_update z (z i)).differentiableAt

theorem maDens_cons_eq_zero {D : ℕ} (f : (Fin (D + 1) → ℂ) → ℝ) (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ)
    (y : Fin (D + 1) → ℂ) (h : f =ᶠ[𝓝 y] fun _ => 0) : maDens (Fin.cons f ψ) y = 0 := by
  have h0 : hessC f y = ((0 : ℝ) : ℂ) • hessC (fun _ => (0 : ℝ)) y := by
    rw [ReciprocityTheory.AnForm.M.hessCGerm f _ y h]
    ext i j
    simp [hessC]
  rw [maDens_cons_of_hessC_eq_smul f (fun _ => 0) ψ y 0 h0, zero_mul]

theorem chartDens_congr_weight {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {f f' : (Fin n → ℂ) → ℝ} (φ : Fin d → (Fin n → ℂ) → ℝ) (h : ∀ x ∈ zeroSet J, f x = f' x) :
    chartDens J A f φ = chartDens J A f' φ := by
  funext y
  unfold chartDens sheetSum
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  dsimp only
  rw [h x hx.1]

theorem abs_sheetSum_sub_le {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {y : Fin d → ℂ} (hfin : (fibre J A y).Finite)
    (T₁ T₂ P Q₁ Q₂ R₁ R₂ : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (a b c : ℝ)
    (h : ∀ x ∈ fibre J A y, ∀ s, IsSheetAt J A x s →
      |T₁ x s - T₂ x s| ≤ a * P x s + b * (Q₁ x s - Q₂ x s) + c * (R₁ x s - R₂ x s)) :
    |sheetSum J A T₁ y - sheetSum J A T₂ y| ≤ a * sheetSum J A P y +
      b * (sheetSum J A Q₁ y - sheetSum J A Q₂ y) + c * (sheetSum J A R₁ y - sheetSum J A R₂ y) := by
  classical
  unfold sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs with hs
  · exact h x hx _ hs.choose_spec
  · simp

theorem measurable_chartDens {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hA : IsFiniteProjection J A)
    {f : (Fin n → ℂ) → ℝ} (hf : ContinuousOn f (zeroSet J)) {ψ : Fin d → (Fin n → ℂ) → ℝ}
    (hψ : ∀ i, SmoothNear (zeroSet J) (ψ i)) : Measurable (chartDens J A f ψ) := by
  classical
  rw [chartDens_congr_weight (f' := (zeroSet J).piecewise f 0) ψ
    (fun x hx => by simp [Set.piecewise, hx])]
  exact (SheetSumMeasurable.proof n d J A _ ψ hJ hdim hA
    (hf.measurable_piecewise continuousOn_const (SheetSumMeasurable.isClosed_zeroSet J).measurableSet) hψ).1

theorem integrable_chartDens (hM : ChartMassCompact.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hA : IsFiniteProjection J A) {f : (Fin n → ℂ) → ℝ} (hf : ContinuousOn f (zeroSet J))
    {ψ : Fin d → (Fin n → ℂ) → ℝ} (hψ : ∀ i, SmoothNear (zeroSet J) (ψ i))
    (hc : HasCompactSupport f ∨ ∃ i, HasCompactSupport (ψ i)) : Integrable (chartDens J A f ψ) :=
  (hM n d J A f ψ hJ hdim hA hf hψ hc).mono' (measurable_chartDens hJ hdim hA hf hψ).aestronglyMeasurable
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using abs_chartDens_le J A f ψ y)

theorem integrable_ball (hM : ChartMassCompact.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hA : IsFiniteProjection J A) (R : ℝ) {w : (Fin n → ℂ) → ℝ} (hw : Continuous w)
    {ψ : Fin d → (Fin n → ℂ) → ℝ} (hψ : ∀ i, SmoothNear (zeroSet J) (ψ i)) :
    Integrable (chartAbsDens J A ((Metric.closedBall 0 R).indicator w) ψ) ∧
      Integrable (chartDens J A ((Metric.closedBall 0 R).indicator w) ψ) := by
  set b : (Fin n → ℂ) → ℝ := fun x => max (min 1 (R + 1 - ‖x‖)) 0 with hbdef
  have hbc : Continuous b := (continuous_const.min (continuous_const.sub continuous_norm)).max continuous_const
  have hbs : HasCompactSupport b := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℂ) (R + 1)) fun x hx => ?_
    have hx' : R + 1 - ‖x‖ ≤ 0 := by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
      linarith
    simp [hbdef, min_eq_right (hx'.trans zero_le_one), max_eq_right hx']
  have hb1 : ∀ x ∈ Metric.closedBall (0 : Fin n → ℂ) R, b x = 1 := by
    intro x hx
    have hx' : 1 ≤ R + 1 - ‖x‖ := by
      simp only [Metric.mem_closedBall, dist_zero_right] at hx
      linarith
    simp [hbdef, min_eq_left hx']
  have hmeas : Measurable ((Metric.closedBall (0 : Fin n → ℂ) R).indicator w) :=
    hw.measurable.indicator Metric.isClosed_closedBall.measurableSet
  have hI := hM n d J A (fun x => b x * w x) ψ hJ hdim hA (hbc.mul hw).continuousOn hψ
    (Or.inl (show HasCompactSupport (b * w) from hbs.mul_right))
  have hm := SheetSumMeasurable.proof n d J A _ ψ hJ hdim hA hmeas hψ
  have hIA : Integrable (chartAbsDens J A ((Metric.closedBall 0 R).indicator w) ψ) := by
    refine hI.mono' hm.2.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (chartAbsDens_nonneg J A _ ψ y)]
    have hfin := (FibreBound.proof n d J A hJ hdim hA y).2.1
    have := sheetSum_le_mul hfin 1
      (fun x s => |(Metric.closedBall 0 R).indicator w x * maDens (fun k => ψ k ∘ s) y|)
      (fun x s => |b x * w x * maDens (fun k => ψ k ∘ s) y|) (fun x _ s _ => by
        by_cases hx : x ∈ Metric.closedBall (0 : Fin n → ℂ) R
        · rw [Set.indicator_of_mem hx, hb1 x hx, one_mul, one_mul]
        · rw [Set.indicator_of_notMem hx, zero_mul, abs_zero]
          positivity)
    simpa [chartAbsDens] using this
  exact ⟨hIA, hIA.mono' hm.1.aestronglyMeasurable
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using abs_chartDens_le J A _ ψ y)⟩

theorem two_mul_le_add_div {t : ℝ} (ht : 0 < t) (u v : ℝ) : 2 * u * v ≤ t * u ^ 2 + v ^ 2 / t := by
  have h : 0 ≤ (t * u - v) ^ 2 / t := by positivity
  have e : (t * u - v) ^ 2 / t = t * u ^ 2 - 2 * u * v + v ^ 2 / t := by
    field_simp
    ring
  linarith

theorem term_bound {G F χ mF mχ g₁ g₂ Eχ EF M C t : ℝ} (ht : 0 < t) (hC : 0 ≤ C) (hM : |G * F| ≤ M)
    (hEχ : 0 ≤ Eχ) (hEF : 0 ≤ EF) (h₁ : |g₁| ≤ C * √Eχ * √EF) (h₂ : |g₂| ≤ C * √EF * √Eχ) :
    |G * (χ * mF + F * mχ + g₁ + g₂) - χ * G * mF| ≤
      M * |1 * mχ| + C * t * (1 * Eχ) + C / t * (G ^ 2 * EF) := by
  have key := two_mul_le_add_div ht (√Eχ) (|G| * √EF)
  rw [Real.sq_sqrt hEχ, mul_pow, sq_abs, Real.sq_sqrt hEF] at key
  have hcomm : C * √EF * √Eχ = C * √Eχ * √EF := by ring
  have hsum : |g₁| + |g₂| ≤ 2 * C * (√Eχ * √EF) := by linarith
  calc |G * (χ * mF + F * mχ + g₁ + g₂) - χ * G * mF| = |G * F * mχ + G * (g₁ + g₂)| := by
        congr 1; ring
    _ ≤ |G * F| * |mχ| + |G| * (|g₁| + |g₂|) := by
        refine (abs_add_le _ _).trans (add_le_add (abs_mul _ _).le ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ ≤ M * |mχ| + |G| * (2 * C * (√Eχ * √EF)) :=
        add_le_add (mul_le_mul_of_nonneg_right hM (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hsum (abs_nonneg _))
    _ = M * |mχ| + C * (2 * √Eχ * (|G| * √EF)) := by ring
    _ ≤ M * |mχ| + C * (t * Eχ + G ^ 2 * EF / t) := by gcongr
    _ = M * |1 * mχ| + C * t * (1 * Eχ) + C / t * (G ^ 2 * EF) := by rw [one_mul, one_mul]; ring

theorem final_bound {X M C aI E Φ : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ aI)
    (h : ∀ t > 0, X ≤ M * aI + C * t * E + C / t * Φ) :
    X ≤ max M (2 * C * √(max Φ 1)) * (aI + √E) := by
  have hΦ1 : 0 < max Φ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hv : 0 < √(max Φ 1) := Real.sqrt_pos.2 hΦ1
  have hΦ2 : max Φ 1 = √(max Φ 1) ^ 2 := (Real.sq_sqrt hΦ1.le).symm
  rcases le_or_gt E 0 with hE | hE
  · rw [Real.sqrt_eq_zero'.2 hE, add_zero]
    have hX : X ≤ M * aI := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have ht : 0 < (C * max Φ 1 + 1) / ε := by positivity
      have h0 := h _ ht
      have h1 : C * ((C * max Φ 1 + 1) / ε) * E ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hE
      have h2 : C / ((C * max Φ 1 + 1) / ε) * Φ ≤ C / ((C * max Φ 1 + 1) / ε) * max Φ 1 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      have h3 : C / ((C * max Φ 1 + 1) / ε) * max Φ 1 ≤ ε := by
        rw [div_div_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg hC hΦ1.le]
      linarith
    exact hX.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ha)
  · have hu : 0 < √E := Real.sqrt_pos.2 hE
    have hE2 : E = √E ^ 2 := (Real.sq_sqrt hE.le).symm
    have h0 := h (√(max Φ 1) / √E) (by positivity)
    have h1 : C * (√(max Φ 1) / √E) * E = C * √E * √(max Φ 1) := by
      rw [hE2, Real.sqrt_sq hu.le]
      field_simp
    have h2 : C / (√(max Φ 1) / √E) * Φ ≤ C * √E * √(max Φ 1) := by
      calc C / (√(max Φ 1) / √E) * Φ ≤ C / (√(max Φ 1) / √E) * max Φ 1 :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
        _ = C * √E * √(max Φ 1) := by
            rw [hΦ2, Real.sqrt_sq hv.le]
            field_simp
    calc X ≤ M * aI + (2 * C * √(max Φ 1)) * √E := by linarith
      _ ≤ max M (2 * C * √(max Φ 1)) * aI + max M (2 * C * √(max Φ 1)) * √E :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) ha)
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hu.le)
      _ = max M (2 * C * √(max Φ 1)) * (aI + √E) := by ring

end CutOffBoundaryBound

open CutOffBoundaryBound in

theorem CutOffBoundaryBound.proof (hM : ChartMassCompact.Statement) (hL : MaDensLeibniz.Statement)
    (hN : EnergyDensNonneg.Statement) (hS : GradDensSheetBound.Statement) :
    CutOffBoundaryBound.Statement := by
  intro n d J A F G φ hJ hdim hA hF hG hφ hc
  obtain ⟨UF, hUFo, hZF, hFs⟩ := hF
  obtain ⟨UG, hUGo, hZG, hGs⟩ := hG
  choose Uφ hUφo hZφ hφs using hφ
  have hUo : IsOpen (UF ∩ UG ∩ ⋂ i, Uφ i) := (hUFo.inter hUGo).inter (isOpen_iInter_of_finite hUφo)
  set U := UF ∩ UG ∩ ⋂ i, Uφ i with hUdef
  have hZU : zeroSet J ⊆ U := Set.subset_inter (Set.subset_inter hZF hZG) (Set.subset_iInter hZφ)
  have hFU : ContDiffOn ℝ ∞ F U := hFs.mono fun x hx => hx.1.1
  have hGU : ContDiffOn ℝ ∞ G U := hGs.mono fun x hx => hx.1.2
  have hφU : ∀ i, ContDiffOn ℝ ∞ (φ i) U := fun i => (hφs i).mono fun x hx => Set.mem_iInter.1 hx.2 i
  have hFc : ContinuousOn F (zeroSet J) := hFU.continuousOn.mono hZU
  have hGc : ContinuousOn G (zeroSet J) := hGU.continuousOn.mono hZU
  have hle2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hZc := SheetSumMeasurable.isClosed_zeroSet J

  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Fin n → ℂ)
  have hK : IsCompact (zeroSet J ∩ Metric.closedBall (0 : Fin n → ℂ) R) :=
    (isCompact_closedBall 0 R).inter_left hZc
  obtain ⟨C₁, hC₁0, hC₁⟩ := hS n d φ U _ hUo hK (fun x hx => hZU hx.1)
    (fun i => (hφU i).of_le hle2)
  obtain ⟨M₀, hM₀⟩ := (hc.isCompact.inter_left hZc).exists_bound_of_continuousOn
    (f := fun x => G x * F x) ((hGc.mul hFc).mono Set.inter_subset_left)
  have hMb : ∀ x ∈ zeroSet J, |G x * F x| ≤ max M₀ 0 := by
    intro x hx
    by_cases hxF : x ∈ tsupport F
    · exact (by simpa [Real.norm_eq_abs] using hM₀ x ⟨hx, hxF⟩ : |G x * F x| ≤ M₀).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hxF, mul_zero, abs_zero]
      exact le_max_right _ _

  have hcons : ∀ (f : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ), SmoothNear (zeroSet J) f →
      (∀ i, SmoothNear (zeroSet J) (ψ i)) → ∀ i, SmoothNear (zeroSet J) (vecCons f ψ i) := by
    intro f ψ hf hψ i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hf
    · simpa using hψ i
  have hω : ∀ i : Fin d, SmoothNear (zeroSet J) ((fun _ => euclPot) i : (Fin n → ℂ) → ℝ) :=
    fun _ => smoothNear_of_contDiff (contDiff_euclPot n)
  have hφn : ∀ i, SmoothNear (zeroSet J) (φ i) := fun i => ⟨U, hUo, hZU, hφU i⟩
  have hFn : SmoothNear (zeroSet J) F := ⟨U, hUo, hZU, hFU⟩
  have hF2n : SmoothNear (zeroSet J) (fun x => F x ^ 2 / 2) := ⟨U, hUo, hZU, (hFU.pow 2).div_const 2⟩
  have hF2c : HasCompactSupport (fun x => F x ^ 2 / 2) := hc.mono fun x hx h0 => hx (by simp [h0])
  have hf₁ := integrable_chartDens hM hJ hdim hA (f := fun x => G x ^ 2) (hGc.pow 2) (hcons _ _ hF2n hω)
    (Or.inr ⟨0, by rw [Matrix.cons_val_zero]; exact hF2c⟩)
  have hf₂ := integrable_chartDens hM hJ hdim hA (f := fun x => G x ^ 2 * F x) ((hGc.pow 2).mul hFc) (hcons _ _ hFn hω)
    (Or.inr ⟨0, by rw [Matrix.cons_val_zero]; exact hc⟩)
  set Φ := ∫ y, (chartDens J A (fun x => G x ^ 2) (vecCons (fun x => F x ^ 2 / 2) fun _ => euclPot) y -
    chartDens J A (fun x => G x ^ 2 * F x) (vecCons F fun _ => euclPot) y) with hΦ
  refine ⟨R, max (max M₀ 0) (2 * C₁ * √(max Φ 1)), fun χ hχ => ?_⟩
  have hχc : Continuous χ := hχ.continuous
  have hχn : SmoothNear (zeroSet J) χ := smoothNear_of_contDiff hχ
  have hχFn : SmoothNear (zeroSet J) (fun x => χ x * F x) := ⟨U, hUo, hZU, hχ.contDiffOn.mul hFU⟩
  have hχ2n : SmoothNear (zeroSet J) (fun x => χ x ^ 2 / 2) := smoothNear_of_contDiff ((hχ.pow 2).div_const 2)
  have hD₁ := integrable_chartDens hM hJ hdim hA hGc (hcons _ _ hχFn hφn)
    (Or.inr ⟨0, by rw [Matrix.cons_val_zero]; exact (hc.mul_left : HasCompactSupport (χ * F))⟩)
  have hD₂ := integrable_chartDens hM hJ hdim hA (f := fun x => χ x * G x) (hχc.continuousOn.mul hGc) (hcons _ _ hFn hφn)
    (Or.inr ⟨0, by rw [Matrix.cons_val_zero]; exact hc⟩)
  have ha := (integrable_ball hM hJ hdim hA R (w := fun _ => (1 : ℝ)) continuous_const (hcons _ _ hχn hφn)).1
  have he₁ := (integrable_ball hM hJ hdim hA R (w := fun _ => (1 : ℝ)) continuous_const (hcons _ _ hχ2n hω)).2
  have he₂ := (integrable_ball hM hJ hdim hA R hχc (hcons _ _ hχn hω)).2

  have key : ∀ t > 0, ∀ y, |chartDens J A G (vecCons (fun x => χ x * F x) φ) y -
      chartDens J A (fun x => χ x * G x) (vecCons F φ) y| ≤
      max M₀ 0 * chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1) (vecCons χ φ) y +
      C₁ * t * (chartDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
          (vecCons (fun x => χ x ^ 2 / 2) fun _ => euclPot) y -
        chartDens J A ((Metric.closedBall 0 R).indicator χ) (vecCons χ fun _ => euclPot) y) +
      C₁ / t * (chartDens J A (fun x => G x ^ 2) (vecCons (fun x => F x ^ 2 / 2) fun _ => euclPot) y -
        chartDens J A (fun x => G x ^ 2 * F x) (vecCons F fun _ => euclPot) y) := by
    intro t ht y
    have hfin := (FibreBound.proof n (d + 1) J A hJ hdim hA y).2.1
    unfold chartDens chartAbsDens
    refine abs_sheetSum_sub_le hfin _ _ _ _ _ _ _ _ _ _ fun x hx s hs => ?_
    obtain ⟨hxZ, hAx⟩ := hx
    have hsx : s y = x := by
      obtain ⟨_, _, _, _, h, -⟩ := hs
      rw [← hAx]
      exact h
    have han : AnalyticAt ℂ s y := by
      rw [← hAx]
      exact analyticAt_of_isSheetAt hs
    have hsc : ContDiffAt ℝ 2 s y := han.restrictScalars.contDiffAt
    have hxU : s y ∈ U := hsx ▸ hZU hxZ
    have c2 : ∀ g : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ g U → ContDiffAt ℝ 2 (g ∘ s) y := fun g hg =>
      ((hg.contDiffAt (hUo.mem_nhds hxU)).of_le hle2).comp y hsc
    have hχs := c2 χ hχ.contDiffOn
    have hFs' := c2 F hFU
    simp only [vecCons_comp]
    have e₂ : maDens (Fin.cons ((fun x => χ x ^ 2 / 2) ∘ s) fun _ => euclPot ∘ s) y =
        (χ ∘ s) y * maDens (Fin.cons (χ ∘ s) fun _ => euclPot ∘ s) y +
          gradDens (fun _ => euclPot ∘ s) (χ ∘ s) (χ ∘ s) y :=
      (hL d (fun _ => euclPot ∘ s) (χ ∘ s) (χ ∘ s) y hχs hχs).2
    have e₃ : maDens (Fin.cons ((fun x => F x ^ 2 / 2) ∘ s) fun _ => euclPot ∘ s) y =
        (F ∘ s) y * maDens (Fin.cons (F ∘ s) fun _ => euclPot ∘ s) y +
          gradDens (fun _ => euclPot ∘ s) (F ∘ s) (F ∘ s) y :=
      (hL d (fun _ => euclPot ∘ s) (F ∘ s) (F ∘ s) y hFs' hFs').2
    rw [e₂, e₃]
    simp only [Function.comp_apply, hsx]
    have hEχ := hN n d s y (χ ∘ s) han
    have hEF := hN n d s y (F ∘ s) han
    have hQ : ∀ m E : ℝ, (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x * (χ x * m + E) -
        (Metric.closedBall (0 : Fin n → ℂ) R).indicator χ x * m =
          (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x * E := by
      intro m E
      by_cases hB : x ∈ Metric.closedBall (0 : Fin n → ℂ) R
      · rw [Set.indicator_of_mem hB, Set.indicator_of_mem hB]
        ring
      · rw [Set.indicator_of_notMem hB, Set.indicator_of_notMem hB]
        ring
    rw [hQ, show ∀ m E : ℝ, G x ^ 2 * (F x * m + E) - G x ^ 2 * F x * m = G x ^ 2 * E from
      fun m E => by ring]
    by_cases hxF : x ∈ tsupport F
    · have hxB : x ∈ Metric.closedBall (0 : Fin n → ℂ) R := hR hxF
      have hKs : s y ∈ zeroSet J ∩ Metric.closedBall (0 : Fin n → ℂ) R := hsx ▸ ⟨hxZ, hxB⟩
      have e₁ : maDens (Fin.cons ((fun x => χ x * F x) ∘ s) fun i => φ i ∘ s) y =
          (χ ∘ s) y * maDens (Fin.cons (F ∘ s) fun i => φ i ∘ s) y +
            (F ∘ s) y * maDens (Fin.cons (χ ∘ s) fun i => φ i ∘ s) y +
              gradDens (fun i => φ i ∘ s) (χ ∘ s) (F ∘ s) y + gradDens (fun i => φ i ∘ s) (F ∘ s) (χ ∘ s) y :=
        (hL d (fun i => φ i ∘ s) (χ ∘ s) (F ∘ s) y hχs hFs').1
      rw [e₁]
      simp only [Function.comp_apply, hsx]
      rw [Set.indicator_of_mem hxB]
      exact term_bound ht hC₁0 (hMb x hxZ) hEχ hEF (hC₁ s y _ _ han hKs) (hC₁ s y _ _ han hKs)
    · have hev : ∀ᶠ z in 𝓝 y, s z ∉ tsupport F :=
        han.continuousAt.preimage_mem_nhds ((isClosed_tsupport F).isOpen_compl.mem_nhds (hsx ▸ hxF))
      have hF0 : (F ∘ s) =ᶠ[𝓝 y] fun _ => 0 :=
        hev.mono fun z hz => image_eq_zero_of_notMem_tsupport (f := F) hz
      have hχF0 : ((fun x => χ x * F x) ∘ s) =ᶠ[𝓝 y] fun _ => 0 :=
        hev.mono fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]
      rw [maDens_cons_eq_zero _ _ y hχF0, maDens_cons_eq_zero _ _ y hF0, mul_zero, mul_zero, sub_zero,
        abs_zero]
      have hi : 0 ≤ (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) x
      exact add_nonneg (add_nonneg (mul_nonneg (le_max_right _ _) (abs_nonneg _))
        (mul_nonneg (mul_nonneg hC₁0 ht.le) (mul_nonneg hi hEχ)))
        (mul_nonneg (div_nonneg hC₁0 ht.le) (mul_nonneg (sq_nonneg _) hEF))

  refine final_bound hC₁0 (integral_nonneg fun y => chartAbsDens_nonneg J A _ _ y)
    fun t ht => ?_
  set D₁ := chartDens J A G (vecCons (fun x => χ x * F x) φ) with hD₁def
  set D₂ := chartDens J A (fun x => χ x * G x) (vecCons F φ) with hD₂def
  set a := chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1) (vecCons χ φ) with hadef
  set e₁ := chartDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
    (vecCons (fun x => χ x ^ 2 / 2) fun _ => euclPot) with he₁def
  set e₂ := chartDens J A ((Metric.closedBall 0 R).indicator χ) (vecCons χ fun _ => euclPot) with he₂def
  set f₁ := chartDens J A (fun x => G x ^ 2) (vecCons (fun x => F x ^ 2 / 2) fun _ => euclPot) with hf₁def
  set f₂ := chartDens J A (fun x => G x ^ 2 * F x) (vecCons F fun _ => euclPot) with hf₂def
  have h1 : chartInt J A G (vecCons (fun x => χ x * F x) φ) -
      chartInt J A (fun x => χ x * G x) (vecCons F φ) = ∫ y, (D₁ y - D₂ y) := (integral_sub hD₁ hD₂).symm
  have h2 : energyInt J A (Metric.closedBall 0 R) χ = ∫ y, (e₁ y - e₂ y) := (integral_sub he₁ he₂).symm
  have h3 : ∫ y, (max M₀ 0 * a y + C₁ * t * (e₁ y - e₂ y) + C₁ / t * (f₁ y - f₂ y)) =
      max M₀ 0 * (∫ y, a y) + C₁ * t * (∫ y, (e₁ y - e₂ y)) + C₁ / t * Φ := by
    rw [integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul]
    all_goals first
      | exact ha.const_mul _
      | exact (he₁.sub he₂).const_mul _
      | exact (hf₁.sub hf₂).const_mul _
      | exact (ha.const_mul _).add ((he₁.sub he₂).const_mul _)
  rw [h1, h2, ← h3]
  refine le_trans ?_ (integral_mono (hD₁.sub hD₂).abs (((ha.const_mul _).add ((he₁.sub he₂).const_mul _)).add
    ((hf₁.sub hf₂).const_mul _)) fun y => key t ht y)
  exact (by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm fun y => D₁ y - D₂ y :
    |∫ y, (D₁ y - D₂ y)| ≤ ∫ y, |D₁ y - D₂ y|)
end

end GroundTheory.Heights₂.Heights
