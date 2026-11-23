import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasurePreservingGlue
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBorelSectionUnitaryOrbitQuadric
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TendstoSublevelDensityProdMeasure
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianNormFibreMeasureEqPolarCoordinates
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTangentBorelSectionQuadric
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryBlockEmbeddingOntoStabiliser
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianNormFibreMeasureFiniteInvariantStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvariantMeasureQuadricMulHaarStabilizer
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrthogonalComplementUnitaryEmbeddingConjBlock
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsDistSectionMulBlockStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PolarSqCompareStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BallVolSuccSqStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralGaussianHermitianNormFibreEqDerivStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSignatureBlocksOfVectorAndFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockPerpEmbeddingOfDiagonalFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeTransportBlockModelStatement

noncomputable section

namespace GlobalTheory.GaugeQuot

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
  GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal Pointwise

variable {P Q P' Q' : ℕ}

theorem tanBall_mul (t r : ℝ) (ht : 0 < t) (_hr : 0 < r) :
    (volume : Measure (ℝ × Sp P Q)) {x | tanSq x < (t * r) ^ 2} =
      ENNReal.ofReal (t ^ Module.finrank ℝ (ℝ × Sp P Q)) *
        volume {x : ℝ × Sp P Q | tanSq x < r ^ 2} := by
  have key : ∀ x : ℝ × Sp P Q, tanSq (t⁻¹ • x) = (t⁻¹) ^ 2 * tanSq x := by
    intro x
    simp only [tanSq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Pi.smul_apply, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    rw [← Finset.mul_sum]
    ring
  have hset : {x : ℝ × Sp P Q | tanSq x < (t * r) ^ 2} = t • {x | tanSq x < r ^ 2} := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne']
    show tanSq x < (t * r) ^ 2 ↔ tanSq (t⁻¹ • x) < r ^ 2
    rw [key, inv_pow, inv_mul_lt_iff₀ (pow_pos ht 2), mul_pow]
  have hH : (volume : Measure (ℝ × Sp P Q)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  rw [hset, Measure.addHaar_smul, abs_of_pos (pow_pos ht _)]

theorem tanBall_ne (r : ℝ) (hr : 0 < r) :
    (volume : Measure (ℝ × Sp P Q)) {x | tanSq x < r} ≠ 0 ∧
      (volume : Measure (ℝ × Sp P Q)) {x | tanSq x < r} ≠ ⊤ := by
  have hH : (volume : Measure (ℝ × Sp P Q)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  refine ⟨(continuous_tanSq.isOpen_preimage _ isOpen_Iio).measure_ne_zero _ ⟨0, ?_⟩, ?_⟩
  · show tanSq (0 : ℝ × Sp P Q) < r
    simp [tanSq, hr]
  · refine (Bornology.IsBounded.measure_lt_top ?_).ne
    refine (Metric.isBounded_closedBall (x := (0 : ℝ × Sp P Q)) (r := Real.sqrt r)).subset ?_
    intro x hx
    have hx' : tanSq x < r := hx
    have hs : 0 ≤ ∑ i, ‖x.2 i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
    have h1 : x.1 ^ 2 ≤ r := by unfold tanSq at hx'; linarith
    have h2 : ∀ i, ‖x.2 i‖ ^ 2 ≤ r := by
      intro i
      have := Finset.single_le_sum (f := fun i => ‖x.2 i‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ i)
      unfold tanSq at hx'
      nlinarith [sq_nonneg x.1]
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    refine ⟨?_, ?_⟩
    · rw [Real.norm_eq_abs]
      exact Real.abs_le_sqrt h1
    · refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      rw [← abs_of_nonneg (norm_nonneg (x.2 i))]
      exact Real.abs_le_sqrt (h2 i)

theorem tendsto_fibSq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (he : SignCompat e)
    {fib : ℝ → Measure (Sp P Q)} (hf : IsDxDq fib) :
    Tendsto (fun r : ℝ => fib (sg (e none)) {y | ptSq e y < r ^ 2} /
      (volume : Measure (ℝ × Sp P' Q')) {x | tanSq x < r ^ 2}) (𝓝[>] 0)
      (𝓝 ((2 : ℝ≥0∞) ^ (P' + Q'))) := by
  have hV0 : ∀ r : ℝ, 0 < r → (volume : Measure (ℝ × Sp P' Q')) {x | tanSq x < r ^ 2} ≠ 0 ∧
      (volume : Measure (ℝ × Sp P' Q')) {x | tanSq x < r ^ 2} ≠ ⊤ :=
    fun r hr => tanBall_ne (r ^ 2) (pow_pos hr 2)
  have hVV : Tendsto (fun r : ℝ => (volume : Measure (ℝ × Sp P' Q')) {x | tanSq x < r ^ 2} /
      (volume : Measure (ℝ × Sp P' Q')) {x | tanSq x < r ^ 2}) (𝓝[>] 0) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (ENNReal.div_self (hV0 r hr).1 (hV0 r hr).2).symm
  have hpi : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
  have hAV : Tendsto (fun r : ℝ => (volume : Measure (ℝ × Sp P' Q'))
      {u | u.1 ∈ Set.Ioo (-Real.pi) Real.pi ∧ ptSq e (polarPt e u) < r ^ 2} /
      (volume : Measure (ℝ × Sp P' Q')) {x | tanSq x < r ^ 2}) (𝓝[>] 0) (𝓝 1) := by
    refine GlobalTheory.CompactDualQuot.tendsto_div_of_squeeze
      (F := fun r : ℝ => (volume : Measure (ℝ × Sp P' Q')) {x | tanSq x < r ^ 2})
      (V := fun r : ℝ => (volume : Measure (ℝ × Sp P' Q')) {x | tanSq x < r ^ 2})
      ENNReal.one_ne_top (fun t r ht hr => tanBall_mul t r ht hr) hVV ?_
    intro t ht
    have hti : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
    have htp : 0 < t⁻¹ := inv_pos.2 (by linarith)
    filter_upwards [GlobalTheory.T.polar_tanSq_ptSq_compare P Q P' Q' e t ht, hpi, self_mem_nhdsWithin] with r hr hr1 hr0
    have hr0' : (0 : ℝ) < r := hr0
    refine ⟨measure_mono fun u hu => ?_, measure_mono fun u hu => ?_⟩
    · have hu' : tanSq u < (t⁻¹ * r) ^ 2 := hu
      have hs : 0 ≤ ∑ i, ‖u.2 i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
      have h1 : u.1 ^ 2 < (t⁻¹ * r) ^ 2 := by unfold tanSq at hu'; linarith
      have h5 := mul_lt_mul_of_pos_right hti hr0'
      have hb : t⁻¹ * r < Real.pi := by linarith [Real.pi_gt_three]
      have habs := abs_lt_of_sq_lt_sq' h1 (mul_pos htp hr0').le
      have hmem : u.1 ∈ Set.Ioo (-Real.pi) Real.pi := ⟨by linarith [habs.1], by linarith [habs.2]⟩
      exact ⟨hmem, (hr u hmem).1 hu'⟩
    · obtain ⟨hmem, hpt⟩ := hu
      exact (hr u hmem).2 hpt
  have hfib : ∀ᶠ r in 𝓝[>] (0 : ℝ), fib (sg (e none)) {y | ptSq e y < r ^ 2} =
      (2 : ℝ≥0∞) ^ (P' + Q') * (volume : Measure (ℝ × Sp P' Q'))
        {u | u.1 ∈ Set.Ioo (-Real.pi) Real.pi ∧ ptSq e (polarPt e u) < r ^ 2} := by
    filter_upwards [hpi, self_mem_nhdsWithin] with r hr1 hr0
    have hr0' : (0 : ℝ) < r := hr0
    refine GlobalTheory.FibrePolar.fibre_eq_polar P Q P' Q' e he fib hf _
      (measurableSet_lt (continuous_ptSq e).measurable measurable_const) ?_
    intro y hy h0
    have hy' : ptSq e y < r ^ 2 := hy
    have hs : 0 ≤ ∑ i, ‖y (e (some i))‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
    unfold ptSq at hy'
    rw [h0, zero_sub, norm_neg, norm_one] at hy'
    nlinarith
  have hlim := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞) ^ (P' + Q')) hAV (Or.inr (ENNReal.pow_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)))
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hfib] with r hr
  rw [hr, mul_div_assoc]

theorem ptSq_act_le (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (g : UpqT P Q) :
    ptSq e (act g (baseVec e)) ≤ 2 * hsDist g := by
  have hcol : ∀ i, act g (baseVec e) i = UpqT.mat g i (e none) := by
    intro i
    simp [act, baseVec, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hsum : ∑ i, ‖(UpqT.mat g - 1) i (e none)‖ ^ 2 ≤ hsDist g := by
    unfold hsDist
    rw [Finset.sum_comm]
    exact Finset.single_le_sum (f := fun j => ∑ i, ‖(UpqT.mat g - 1) i j‖ ^ 2)
      (fun j _ => Finset.sum_nonneg fun i _ => by positivity) (Finset.mem_univ (e none))
  have hsplit : ∑ i, ‖(UpqT.mat g - 1) i (e none)‖ ^ 2 =
      ‖(UpqT.mat g - 1) (e none) (e none)‖ ^ 2 +
        ∑ a, ‖(UpqT.mat g - 1) (e (some a)) (e none)‖ ^ 2 := by
    rw [← e.sum_comp, Fintype.sum_option]
  have h0 : act g (baseVec e) (e none) - 1 = (UpqT.mat g - 1) (e none) (e none) := by
    rw [hcol, Matrix.sub_apply, Matrix.one_apply_eq]
  have h1 : ∀ a, act g (baseVec e) (e (some a)) = (UpqT.mat g - 1) (e (some a)) (e none) := by
    intro a
    rw [hcol, Matrix.sub_apply, Matrix.one_apply_ne (e.injective.ne (Option.some_ne_none a)),
      sub_zero]
  have hnn : 0 ≤ ‖(UpqT.mat g - 1) (e none) (e none)‖ ^ 2 := by positivity
  unfold ptSq
  rw [h0]
  simp only [h1]
  linarith

theorem tendsto_sq_pos : Tendsto (fun r : ℝ => r ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h := ((continuous_pow 2).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) < r := hr
    exact pow_pos hr' 2

theorem tendsto_of_sq {F : ℝ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : Tendsto (fun r : ℝ => F (r ^ 2)) (𝓝[>] 0) (𝓝 c)) : Tendsto F (𝓝[>] 0) (𝓝 c) := by
  have hs : Tendsto Real.sqrt (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : (0 : ℝ) < r := hr
      exact Real.sqrt_pos.2 hr'
  refine (h.comp hs).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : (0 : ℝ) < r := hr
  simp only [Function.comp_apply, Real.sq_sqrt hr'.le]

theorem ballVol_eq (d : ℕ) {r : ℝ} (hr : 0 < r) :
    volume {x : EuclideanSpace ℝ (Fin d) | ‖x‖ ^ 2 < r ^ 2} = ballVol d r := by
  show _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)
  congr 1
  ext x
  show ‖x‖ ^ 2 < r ^ 2 ↔ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r
  rw [mem_ball_zero_iff]
  exact sq_lt_sq₀ (norm_nonneg x) hr.le

private lemma indicator_one_le_indicator_one_of_imp {α β : Type*} {S : Set α} {T : Set β} {a : α} {b : β}
    (h : a ∈ S → b ∈ T) : S.indicator (1 : α → ℝ≥0∞) a ≤ T.indicator 1 b := by
  by_cases ha : a ∈ S
  · simp [ha, h ha]
  · simp [ha]

theorem const_eq_one (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (he : SignCompat e)
    {fib : ℝ → Measure (Sp P Q)} (hf : IsDxDq fib) (j : UpqT P' Q' →* UpqT P Q)
    (hj : IsBlockEmb e j) (hjc : Continuous j) (hjs : ∀ g, act (j g) (baseVec e) = baseVec e)
    {μ : Measure (UpqT P Q)} {μ' : Measure (UpqT P' Q')} [μ'.IsHaarMeasure]
    (h : HasEuclDensity μ) (h' : HasEuclDensity μ')
    (κ : ℝ≥0) (hκ : ∀ s : Sp P Q → UpqT P Q, IsSection (sg (e none)) (baseVec e) s →
      ∀ f : UpqT P Q → ℝ≥0∞, Measurable f →
        ∫⁻ y, (∫⁻ g', f (s y * j g') ∂μ') ∂(fib (sg (e none))) = κ * ∫⁻ g, f g ∂μ) :
    (κ : ℝ≥0∞) = 1 := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P' Q'
  have := i1; have := i2; have := i3; have := i4; have := i5
  have := k1; have := k2; have := k3; have := k4; have := k5
  have hβ : sg (e none) ≠ 0 := sg_ne_zero _
  have := (GlobalTheory.T.hermitianNormFibreMeasure_finite_invariant P Q fib (sg (e none)) hf hβ).1
  obtain ⟨σ, hσ, hσ2⟩ := GlobalTheory.TangentSection.exists_tangent_section P Q P' Q' e
  have hS : ∀ r : ℝ, MeasurableSet {g : UpqT P Q | hsDist g < r ^ 2} := fun r =>
    measurableSet_lt continuous_hsDist.measurable measurable_const
  have hTm : ∀ ρ : ℝ, MeasurableSet {p : Sp P Q × UpqT P' Q' | ptSq e p.1 + hsDist p.2 < ρ} :=
    fun ρ => measurableSet_lt (((continuous_ptSq e).measurable.comp measurable_fst).add
      (continuous_hsDist.measurable.comp measurable_snd)) measurable_const
  have hL : ∀ r : ℝ, ∫⁻ y, (∫⁻ g', {g : UpqT P Q | hsDist g < r ^ 2}.indicator 1 (σ y * j g') ∂μ')
      ∂(fib (sg (e none))) = κ * μ {g | hsDist g < r ^ 2} := by
    intro r
    rw [← lintegral_indicator_one (hS r)]
    exact hκ σ hσ _ (measurable_one.indicator (hS r))
  have ne1 : ∀ y : Sp P Q, ptSq e y < 1 → y (e none) ≠ -1 := by
    intro y hy h1
    have hs : 0 ≤ ∑ i, ‖y (e (some i))‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
    unfold ptSq at hy
    rw [h1, show (-1 : ℂ) - 1 = -2 by norm_num, norm_neg] at hy
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2] at hy
    nlinarith
  have hd1 : Tendsto (fun ρ : ℝ => fib (sg (e none)) {y | ptSq e y < ρ} /
      (volume : Measure (ℝ × Sp P' Q')) {x | tanSq x < ρ}) (𝓝[>] 0)
      (𝓝 ((2 : ℝ≥0∞) ^ (P' + Q'))) :=
    tendsto_of_sq (F := fun ρ : ℝ => fib (sg (e none)) {y | ptSq e y < ρ} /
      (volume : Measure (ℝ × Sp P' Q')) {x | tanSq x < ρ}) (tendsto_fibSq e he hf)
  have hd2 : Tendsto (fun ρ : ℝ => μ' {g | hsDist g < ρ} /
      (volume : Measure (EuclideanSpace ℝ (Fin ((P' + Q') ^ 2)))) {x | ‖x‖ ^ 2 < ρ})
      (𝓝[>] 0) (𝓝 1) := by
    refine tendsto_of_sq (F := fun ρ : ℝ => μ' {g | hsDist g < ρ} /
      (volume : Measure (EuclideanSpace ℝ (Fin ((P' + Q') ^ 2)))) {x | ‖x‖ ^ 2 < ρ}) ?_
    refine (show Tendsto (fun r : ℝ => μ' {g | hsDist g < r ^ 2} / ballVol ((P' + Q') ^ 2) r)
      (𝓝[>] 0) (𝓝 1) from h').congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [← ballVol_eq _ hr]
  have hl2 : ∀ r : ℝ, 0 < r →
      (volume : Measure (EuclideanSpace ℝ (Fin ((P' + Q') ^ 2)))) {x | ‖x‖ ^ 2 < r} ≠ 0 ∧
      (volume : Measure (EuclideanSpace ℝ (Fin ((P' + Q') ^ 2)))) {x | ‖x‖ ^ 2 < r} ≠ ⊤ := by
    intro r hr
    have hq := ballVol_eq ((P' + Q') ^ 2) (Real.sqrt_pos.2 hr)
    rw [Real.sq_sqrt hr.le] at hq
    rw [hq]
    exact ⟨ballVol_ne_zero _ (Real.sqrt_pos.2 hr), ballVol_ne_top _ _⟩
  have hGW : Tendsto (fun ρ : ℝ =>
      ((fib (sg (e none))).prod μ') {p | ptSq e p.1 + hsDist p.2 < ρ} /
      ((volume : Measure (ℝ × Sp P' Q')).prod
        (volume : Measure (EuclideanSpace ℝ (Fin ((P' + Q') ^ 2)))))
        {p | tanSq p.1 + ‖p.2‖ ^ 2 < ρ}) (𝓝[>] 0) (𝓝 ((2 : ℝ≥0∞) ^ (P' + Q') * 1)) :=
    GlobalTheory.SublevelDensity.tendsto_prod_density _ _ _ _ (fib (sg (e none))) volume μ' volume
      (ptSq e) tanSq hsDist (fun x => ‖x‖ ^ 2) _ _ (continuous_ptSq e).measurable
      continuous_tanSq.measurable continuous_hsDist.measurable (continuous_norm.pow 2).measurable
      (ptSq_nonneg e) tanSq_nonneg hsDist_nonneg (fun x => sq_nonneg _)
      (ENNReal.pow_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)) ENNReal.one_ne_top (fun r hr => tanBall_ne r hr)
      hl2 hd1 hd2
  have hk0 : (2 : ℝ≥0∞) ^ (P' + Q') ≠ 0 := pow_ne_zero _ two_ne_zero
  have hkt : (2 : ℝ≥0∞) ^ (P' + Q') ≠ ⊤ := ENNReal.pow_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have hF : Tendsto (fun r : ℝ =>
      ((fib (sg (e none))).prod μ') {p | ptSq e p.1 + hsDist p.2 < r ^ 2} /
      ballVol ((P + Q) ^ 2) r) (𝓝[>] 0) (𝓝 1) := by
    have h1 := ENNReal.Tendsto.mul_const (hGW.comp tendsto_sq_pos)
      (b := ((2 : ℝ≥0∞) ^ (P' + Q'))⁻¹) (Or.inr (ENNReal.inv_ne_top.2 hk0))
    rw [mul_one, ENNReal.mul_inv_cancel hk0 hkt] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [card_eq e, GlobalTheory.T.ballVol_succ_sq_eq_pow_mul_prod P' Q' r hr]
    simp only [Function.comp_apply]
    rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hk0) (Or.inl hkt)]
    ring
  have hA : ∀ t : ℝ, 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ((fib (sg (e none))).prod μ') {p | ptSq e p.1 + hsDist p.2 < (t⁻¹ * r) ^ 2} ≤
        ∫⁻ y, (∫⁻ g', {g : UpqT P Q | hsDist g < r ^ 2}.indicator 1 (σ y * j g') ∂μ')
          ∂(fib (sg (e none))) ∧
      ∫⁻ y, (∫⁻ g', {g : UpqT P Q | hsDist g < r ^ 2}.indicator 1 (σ y * j g') ∂μ')
          ∂(fib (sg (e none))) ≤
        ((fib (sg (e none))).prod μ') {p | ptSq e p.1 + hsDist p.2 < (t * r) ^ 2} := by
    intro t ht
    have htp : 0 < t := by linarith
    have hti : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
    have htip : 0 < t⁻¹ := inv_pos.2 htp
    have ht2 : 1 < t ^ 2 := by nlinarith
    have ht2p : 0 < t ^ 2 := pow_pos htp 2
    obtain ⟨δ, hδ0, hδ⟩ := GlobalTheory.T.ptSq_add_hsDist_comparable_hsDist_mul P Q P' Q' e j hj (t ^ 2) ht2
    have hm : 0 < min δ 1 / 2 := half_pos (lt_min hδ0 one_pos)
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ^ 2 < min δ 1 / 2 := by
      have hc : Tendsto (fun r : ℝ => r ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have h := ((continuous_pow 2).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        simpa using h
      exact hc.eventually (eventually_lt_nhds hm)
    filter_upwards [hev, self_mem_nhdsWithin] with r hr2 hr0
    have hr0' : (0 : ℝ) < r := hr0
    have hmin : min δ 1 ≤ δ := min_le_left _ _
    have hmin1 : min δ 1 ≤ 1 := min_le_right _ _
    have hrr : 0 ≤ r ^ 2 := sq_nonneg r
    have hup : ∀ y, qf y = sg (e none) → ∀ g', σ y * j g' ∈ {g : UpqT P Q | hsDist g < r ^ 2} →
        (y, g') ∈ {p : Sp P Q × UpqT P' Q' | ptSq e p.1 + hsDist p.2 < (t * r) ^ 2} := by
      intro y hy g' hg
      have hg' : hsDist (σ y * j g') < r ^ 2 := hg
      have hact : act (σ y * j g') (baseVec e) = y := by
        rw [GlobalTheory.RealPlaceCompare.act_mul, hjs, hσ.2 y hy]
      have hp := ptSq_act_le e (σ y * j g')
      rw [hact] at hp
      have hsm : ptSq e y < min δ 1 := by linarith
      obtain ⟨hn1, hn2⟩ := hσ2 y hy (ne1 y (by linarith))
      have hb := (hδ y (σ y) (by linarith) (hσ.2 y hy) hn1 hn2 g').1
      have h3 : t ^ 2 * hsDist (σ y * j g') < t ^ 2 * r ^ 2 := mul_lt_mul_of_pos_left hg' ht2p
      show ptSq e y + hsDist g' < (t * r) ^ 2
      rw [mul_pow]
      linarith
    have hlo : ∀ y, qf y = sg (e none) → ∀ g',
        (y, g') ∈ {p : Sp P Q × UpqT P' Q' | ptSq e p.1 + hsDist p.2 < (t⁻¹ * r) ^ 2} →
        σ y * j g' ∈ {g : UpqT P Q | hsDist g < r ^ 2} := by
      intro y hy g' hg
      have hg' : ptSq e y + hsDist g' < (t⁻¹ * r) ^ 2 := hg
      have htr1 : t⁻¹ * r ≤ r := by
        have := mul_lt_mul_of_pos_right hti hr0'
        linarith
      have htr : (t⁻¹ * r) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (mul_pos htip hr0').le htr1 2
      have hd := hsDist_nonneg g'
      have hsm : ptSq e y < min δ 1 := by linarith
      obtain ⟨hn1, hn2⟩ := hσ2 y hy (ne1 y (by linarith))
      have hb := (hδ y (σ y) (by linarith) (hσ.2 y hy) hn1 hn2 g').2
      have h3 : t ^ 2 * (ptSq e y + hsDist g') < t ^ 2 * (t⁻¹ * r) ^ 2 :=
        mul_lt_mul_of_pos_left hg' ht2p
      have h4 : t ^ 2 * (t⁻¹ * r) ^ 2 = r ^ 2 := by
        rw [mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ htp.ne', one_pow, one_mul]
      show hsDist (σ y * j g') < r ^ 2
      linarith
    refine ⟨?_, ?_⟩
    · rw [Measure.prod_apply (hTm _)]
      refine lintegral_mono_ae ?_
      filter_upwards [GlobalTheory.RealPlaceCompare.ae_qf hf (sg (e none))] with y hy
      rw [← lintegral_indicator_one (measurable_prodMk_left (hTm _))]
      exact lintegral_mono fun g' => indicator_one_le_indicator_one_of_imp (hlo y hy g')
    · rw [Measure.prod_apply (hTm _)]
      refine lintegral_mono_ae ?_
      filter_upwards [GlobalTheory.RealPlaceCompare.ae_qf hf (sg (e none))] with y hy
      rw [← lintegral_indicator_one (measurable_prodMk_left (hTm _))]
      exact lintegral_mono fun g' => indicator_one_le_indicator_one_of_imp (hup y hy g')
  have hLV := GlobalTheory.CompactDualQuot.tendsto_div_of_squeeze
    (F := fun r : ℝ => ((fib (sg (e none))).prod μ') {p | ptSq e p.1 + hsDist p.2 < r ^ 2})
    (V := ballVol ((P + Q) ^ 2))
    (A := fun r : ℝ => ∫⁻ y, (∫⁻ g', {g : UpqT P Q | hsDist g < r ^ 2}.indicator 1
      (σ y * j g') ∂μ') ∂(fib (sg (e none))))
    ENNReal.one_ne_top (fun t r ht hr => ballVol_mul _ t r ht hr) hF hA
  have hκV : Tendsto (fun r : ℝ => (∫⁻ y, (∫⁻ g', {g : UpqT P Q | hsDist g < r ^ 2}.indicator 1
      (σ y * j g') ∂μ') ∂(fib (sg (e none)))) / ballVol ((P + Q) ^ 2) r) (𝓝[>] 0)
      (𝓝 ((κ : ℝ≥0∞) * 1)) := by
    refine (ENNReal.Tendsto.const_mul (show Tendsto (fun r : ℝ => μ {g | hsDist g < r ^ 2} /
      ballVol ((P + Q) ^ 2) r) (𝓝[>] 0) (𝓝 1) from h) (Or.inr ENNReal.coe_ne_top)).congr' ?_
    filter_upwards with r
    rw [hL r, mul_div_assoc]
  have := tendsto_nhds_unique hκV hLV
  rwa [mul_one] at this

theorem quot_formula (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (he : SignCompat e)
    {fib : ℝ → Measure (Sp P Q)} (hf : IsDxDq fib)
    {μ : Measure (UpqT P Q)} {μ' : Measure (UpqT P' Q')} (hμ : μ.IsHaarMeasure)
    (hμ' : μ'.IsHaarMeasure) (h : HasEuclDensity μ) (h' : HasEuclDensity μ')
    {x₀ : Sp P Q} (hx₀ : qf x₀ = sg (e none)) {A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ}
    {j : UpqT P' Q' → UpqT P Q} (hA : IsPerpEmb x₀ A j)
    {s : Sp P Q → UpqT P Q} (hs : IsSection (sg (e none)) x₀ s)
    {f : UpqT P Q → ℝ≥0∞} (hfm : Measurable f) :
    ∫⁻ g, f g ∂μ = ∫⁻ y, (∫⁻ g', f (s y * j g') ∂μ') ∂(fib (sg (e none))) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  have := i1; have := i2; have := i3; have := i4; have := i5
  obtain ⟨j₀, hj₀, hj₀c, hj₀r⟩ := GlobalTheory.BlockEmbedding.exists_blockEmb P Q P' Q' e he
  obtain ⟨g₀, hg₀, hjconj⟩ :=
    GlobalTheory.CompactDualQuot.PerpConj.perp_conj P Q P' Q' e he j₀ hj₀ x₀ A j hx₀ hA
  have hβ : sg (e none) ≠ 0 := sg_ne_zero _
  obtain ⟨hfin, hinv⟩ := GlobalTheory.T.hermitianNormFibreMeasure_finite_invariant P Q fib (sg (e none)) hf hβ
  obtain ⟨κ, hκ⟩ := GlobalTheory.QuadricHaar.quadric_haar P Q P' Q' (sg (e none)) (baseVec e) j₀
    (fib (sg (e none))) μ μ' hj₀c hj₀r hfin (GlobalTheory.RealPlaceCompare.ae_qf hf _) hinv hμ hμ'
  have := hμ'
  have hjs : ∀ g, act (j₀ g) (baseVec e) = baseVec e := fun g => by
    have hm : j₀ g ∈ Set.range j₀ := ⟨g, rfl⟩
    rw [hj₀r] at hm
    exact hm
  have hκ1 := const_eq_one e he hf j₀ hj₀ hj₀c.continuous hjs h h' κ hκ
  have hs' : IsSection (sg (e none)) (baseVec e) (fun y => s y * g₀) := by
    refine ⟨hs.1.mul_const g₀, fun y hy => ?_⟩
    rw [GlobalTheory.RealPlaceCompare.act_mul, hg₀, hs.2 y hy]
  have key := hκ (fun y => s y * g₀) hs' (fun g => f (g * g₀⁻¹))
    (hfm.comp (measurable_mul_const _))
  simp only [hκ1, one_mul] at key
  have : μ.IsMulRightInvariant := GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure P Q μ hμ
  have hr : ∫⁻ g, f (g * g₀⁻¹) ∂μ = ∫⁻ g, f g ∂μ := lintegral_mul_right_eq_self f g₀⁻¹
  rw [← hr, ← key]
  simp only [hjconj, mul_assoc]

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.GaussMean

theorem qf_comp {n : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (y : Fin n → ℂ) : qf (fun i => y (f i)) = qEps ε y := by
  unfold qf qEps
  rw [← f.sum_comp, Fintype.sum_sum_type]
  simp only [hf.1, hf.2, if_true, Bool.false_eq_true, if_false, one_mul, neg_one_mul,
    Finset.sum_neg_distrib, Complex.normSq_eq_norm_sq]
  ring

theorem gaussSp_comp {n : ℕ} (f : Fin P ⊕ Fin Q ≃ Fin n) (y : Fin n → ℂ) :
    gaussSp (fun i => y (f i)) = gauss y := by
  unfold gaussSp gauss
  rw [Equiv.sum_comp f (fun k => ‖y k‖ ^ 2)]

theorem integral_sublevel {n : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (t : ℝ) : ∫ y in {y : Sp P Q | qf y ≤ t}, gaussSp y =
      ∫ y in {y : Fin n → ℂ | qEps ε y ≤ t}, gauss y := by
  let E := (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℂ) f).symm
  have hE : MeasurePreserving E volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℂ) f).symm _
  have hEy : ∀ y : Fin n → ℂ, E y = fun i => y (f i) := by
    intro y
    rw [MeasurableEquiv.symm_apply_eq]
    funext k
    obtain ⟨i, rfl⟩ := f.surjective k
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  have hpre : E ⁻¹' {y : Sp P Q | qf y ≤ t} = {y | qEps ε y ≤ t} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hEy, qf_comp hf]
  have h := hE.setIntegral_preimage_emb E.measurableEmbedding gaussSp {y : Sp P Q | qf y ≤ t}
  rw [← h, hpre]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hEy, gaussSp_comp]

theorem act_symm {n : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (k : Formalism.REAL.UJ ε) (y : Fin n → ℂ) :
    act (hf.equiv.symm k) (fun i => y (f i)) = fun i => (uMat k *ᵥ y) (f i) := by
  have h : uMat k = Matrix.reindex f f (UpqT.mat (hf.equiv.symm k)) := by
    have h0 := hf.umat_equiv (hf.equiv.symm k)
    rw [ContinuousMulEquiv.apply_symm_apply] at h0
    exact h0
  funext i
  simp only [act, Matrix.mulVec, dotProduct]
  rw [h, ← f.sum_comp]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

theorem lintegral_map_symm {n : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (c : ℝ≥0∞) (φ : UpqT P Q → ℝ≥0∞) :
    ∫⁻ g, φ g ∂((c • Formalism.REAL.muG ε).map hf.equiv.symm) =
      c * ∫⁻ k, φ (hf.equiv.symm k⁻¹) ∂(Formalism.REAL.muG ε) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  have := i5
  have : (Formalism.REAL.muG ε).IsInvInvariant := ⟨Formalism.REAL.invInvariant n ε⟩
  have hme : MeasurableEmbedding (hf.equiv.symm : Formalism.REAL.UJ ε → UpqT P Q) :=
    (hf.equiv.symm.toHomeomorph.toMeasurableEquiv).measurableEmbedding
  rw [hme.lintegral_map, lintegral_smul_measure]
  congr 1
  exact (lintegral_inv_eq_self (μ := Formalism.REAL.muG ε) (fun k => φ (hf.equiv.symm k))).symm

theorem isHaar_map_symm {n : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    {c : ℝ} (hc : 0 < c) :
    ((ENNReal.ofReal c • Formalism.REAL.muG ε).map hf.equiv.symm).IsHaarMeasure := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  have := i1; have := i2; have := i3; have := i4; have := i5
  have : (ENNReal.ofReal c • Formalism.REAL.muG ε).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul _ (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top
  exact ContinuousMulEquiv.isHaarMeasure_map (μ := ENNReal.ofReal c • Formalism.REAL.muG ε) hf.equiv.symm

theorem gauge_quotient : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ) (j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε), qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → (∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g) → ∀ c c' : ℝ, IsGauge ε c → IsGauge ε' c' → ∀ b : Formalism.REAL.UJ ε → ENNReal, Measurable b → (∀ g, ENNReal.ofReal c' * ∫⁻ h, b (j h * g) ∂(Formalism.REAL.muG ε') = 1) → ENNReal.ofReal c * ∫⁻ g, ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ x₀)) * b g ∂(Formalism.REAL.muG ε) = ENNReal.ofReal (2 ^ (n + 1) * gaussDens ε (GlobalTheory.GaussMean.sgn ℝ s)) := by
  intro n ε ε' s x₀ B j hq hperp hB hj c c' hc hc' b hb hbint
  obtain ⟨P, Q, f, hf⟩ := GlobalTheory.Mem.Vol.Scale.exists_sorts ε
  obtain ⟨P', Q', f', hf'⟩ := GlobalTheory.Mem.Vol.Scale.exists_sorts ε'
  obtain ⟨e, he, hes⟩ := GlobalTheory.T.exists_signature_blocks_of_vector_and_frame n ε ε' s x₀ B hq hperp hB P Q P' Q' f f' hf hf'
  have hA := GlobalTheory.T.blockPerpEmbedding_of_diagonal_frame n ε ε' s x₀ B j hq hperp hB hj P Q P' Q' f f' hf hf'
  obtain ⟨hc0, hcE⟩ := GlobalTheory.T.riemannianHaarGauge_transport_block_model (n + 1) ε c P Q f hf hc
  obtain ⟨hc0', hcE'⟩ := GlobalTheory.T.riemannianHaarGauge_transport_block_model n ε' c' P' Q' f' hf' hc'
  obtain ⟨fib, hfib⟩ := GlobalTheory.RealPlaceCompare.exists_isDxDq P Q
  have hβ : sg (e none) ≠ 0 := GlobalTheory.CompactDualQuot.sg_ne_zero _
  have hx : qf (fun i => x₀ (f i)) = sg (e none) := by rw [qf_comp hf, hq, hes]
  obtain ⟨σ, hσ⟩ := GlobalTheory.QuadricSection.exists_isSection P Q _ (fun i => x₀ (f i)) hβ hx
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  have := i5
  have hcu : Continuous (fun k : Formalism.REAL.UJ ε => uMat k) :=
    Units.continuous_val.comp continuous_subtype_val
  have hcg : Continuous (fun k : Formalism.REAL.UJ ε => gauss (uMat k *ᵥ x₀)) := by
    unfold gauss
    refine Real.continuous_exp.comp (continuous_finsetSum _ fun i _ => ?_).neg
    exact ((continuous_apply i).comp (hcu.matrix_mulVec continuous_const)).norm.pow 2
  have huinv : ∀ k : Formalism.REAL.UJ ε, uMat k⁻¹ = (uMat k)⁻¹ := fun k => by
    rw [show uMat k⁻¹ = (((k : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)⁻¹ :
      (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) from rfl,
      Matrix.coe_units_inv]
  let φ : UpqT P Q → ℝ≥0∞ := fun g =>
    ENNReal.ofReal (gauss (uMat (hf.equiv g) *ᵥ x₀)) * b (hf.equiv g)⁻¹
  have hφm : Measurable φ :=
    (hcg.measurable.comp hf.measurable_equiv).ennreal_ofReal.mul
      (hb.comp (measurable_inv.comp hf.measurable_equiv))
  have hQ := quot_formula e he hfib (isHaar_map_symm hf hc0) (isHaar_map_symm hf' hc0') hcE hcE'
    hx hA hσ hφm
  have hin : ∀ᵐ y ∂(fib (sg (e none))), ∫⁻ g', φ (σ y * hf.equiv.symm (j (hf'.equiv g')))
      ∂((ENNReal.ofReal c' • Formalism.REAL.muG ε').map hf'.equiv.symm) =
        ENNReal.ofReal (gaussSp y) := by
    filter_upwards [GlobalTheory.RealPlaceCompare.ae_qf hfib (sg (e none))] with y hy
    have hyk : (fun i => (uMat (hf.equiv (σ y)) *ᵥ x₀) (f i)) = y := by
      rw [← act_symm hf (hf.equiv (σ y)) x₀, ContinuousMulEquiv.symm_apply_apply]
      exact hσ.2 y hy
    have hpt : ∀ g', φ (σ y * hf.equiv.symm (j (hf'.equiv g'))) =
        ENNReal.ofReal (gaussSp y) * b (j (hf'.equiv g'⁻¹) * (hf.equiv (σ y))⁻¹) := by
      intro g'
      have h1 : hf.equiv (σ y * hf.equiv.symm (j (hf'.equiv g'))) =
          hf.equiv (σ y) * j (hf'.equiv g') := by
        rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
      have h2 : uMat (hf.equiv (σ y) * j (hf'.equiv g')) *ᵥ x₀ = uMat (hf.equiv (σ y)) *ᵥ x₀ := by
        have h5 : uMat (hf.equiv (σ y) * j (hf'.equiv g')) =
            uMat (hf.equiv (σ y)) * uMat (j (hf'.equiv g')) := rfl
        rw [h5, ← Matrix.mulVec_mulVec, (hj _).1]
      have h3 : (hf.equiv (σ y) * j (hf'.equiv g'))⁻¹ =
          j (hf'.equiv g'⁻¹) * (hf.equiv (σ y))⁻¹ := by
        simp [_root_.mul_inv_rev, map_inv]
      have h4 : gauss (uMat (hf.equiv (σ y)) *ᵥ x₀) = gaussSp y := by
        rw [← gaussSp_comp f (uMat (hf.equiv (σ y)) *ᵥ x₀), hyk]
      show ENNReal.ofReal (gauss (uMat (hf.equiv (σ y * hf.equiv.symm (j (hf'.equiv g')))) *ᵥ x₀)) *
        b (hf.equiv (σ y * hf.equiv.symm (j (hf'.equiv g'))))⁻¹ = _
      rw [h1, h2, h3, h4]
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_map_symm hf' (ENNReal.ofReal c')]
    simp only [map_inv, ContinuousMulEquiv.apply_symm_apply, inv_inv]
    rw [hbint, mul_one]
  have hfun : (fun t : ℝ => ∫ y in {y : Sp P Q | qf y ≤ t}, gaussSp y) =
      fun t => ∫ y in {y : Fin (n + 1) → ℂ | qEps ε y ≤ t}, gauss y :=
    funext fun t => integral_sublevel hf t
  have hder := ((GlobalTheory.T.gaussianQuadricDensity_exists_pos_continuous (n + 1) ε).1 (sg (e none)) hβ).1
  rw [← hfun] at hder
  have hL := lintegral_map_symm hf (ENNReal.ofReal c) φ
  calc ENNReal.ofReal c * ∫⁻ g, ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ x₀)) * b g ∂(Formalism.REAL.muG ε)
      = ∫⁻ g, φ g ∂((ENNReal.ofReal c • Formalism.REAL.muG ε).map hf.equiv.symm) := by
        rw [hL]
        congr 1
        refine lintegral_congr fun k => ?_
        simp only [φ, ContinuousMulEquiv.apply_symm_apply, inv_inv, huinv]
    _ = ∫⁻ y, (∫⁻ g', φ (σ y * hf.equiv.symm (j (hf'.equiv g')))
          ∂((ENNReal.ofReal c' • Formalism.REAL.muG ε').map hf'.equiv.symm)) ∂(fib (sg (e none))) := hQ
    _ = ∫⁻ y, ENNReal.ofReal (gaussSp y) ∂(fib (sg (e none))) := lintegral_congr_ae hin
    _ = ENNReal.ofReal (2 ^ (n + 1) * gaussDens ε (GlobalTheory.GaussMean.sgn ℝ s)) := by
        rw [GlobalTheory.T.lintegral_gaussian_hermitianNormFibre_eq_deriv P Q fib (sg (e none)) _ hfib hβ hder, hes,
          GlobalTheory.Mem.Vol.Scale.Sorts.add_eq f]

end GlobalTheory.GaugeQuot
