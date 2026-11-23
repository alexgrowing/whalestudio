import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasurePreservingGlue
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBorelSectionUnitaryOrbitQuadric
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryExpLieBallComparableEntryGaugeStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TendstoSublevelDensityProdMeasureStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianNormFibreMeasureEqPolarCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadricPointGaugePolarCoordinatesCompareTangentGStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryLieVolumeBallSplitBasisVectorStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTangentBorelSectionQuadricStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadricPointGaugeSectionMulBlockCompareStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryBlockEmbeddingOntoStabiliserStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianNormFibreMeasureFiniteInvariantStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvariantMeasureQuadricMulHaarStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsOrthogonalComplementIsometryEmbeddingTraStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrthogonalComplementUnitaryEmbeddingConjBlockStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PositiveDefiniteUnitSphereMassProofStatement

noncomputable section

namespace GlobalTheory.CompactDualQuot

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal NNReal Pointwise

variable {P Q P' Q' : ℕ}

theorem addHaar_sublevel {V : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (lam : Measure V) [lam.IsAddHaarMeasure] (N : V → ℝ)
    (hc : Continuous N) (hs : ∀ (t : ℝ) (x : V), 0 ≤ t → N (t • x) = t * N x)
    (hK : ∀ r, IsCompact {x | N x ≤ r}) :
    (∀ t r : ℝ, 0 < t → 0 < r → lam {x | N x < t * r} =
      ENNReal.ofReal (t ^ Module.finrank ℝ V) * lam {x | N x < r}) ∧
    ∀ r : ℝ, 0 < r → lam {x | N x < r} ≠ 0 ∧ lam {x | N x < r} ≠ ⊤ := by
  let φ : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv
  constructor
  · intro t r ht hr
    let m : Measure (Fin (Module.finrank ℝ V) → ℝ) := lam.map φ
    haveI : m.IsAddHaarMeasure := φ.isAddHaarMeasure_map lam
    have hm : ∀ ρ : ℝ, lam {x | N x < ρ} = m {z | N (φ.symm z) < ρ} := fun ρ => by
      refine Eq.trans ?_ (Measure.map_apply φ.continuous.measurable
        (isOpen_lt (hc.comp φ.symm.continuous) continuous_const).measurableSet).symm
      congr 1; ext x; simp
    have e : {z | N (φ.symm z) < t * r} = t • {z | N (φ.symm z) < r} := by
      ext z
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', Set.mem_setOf_eq, Set.mem_setOf_eq, map_smul,
        hs _ _ (inv_pos.2 ht).le, inv_mul_lt_iff₀ ht]
    rw [hm, hm, e, Measure.addHaar_smul_of_nonneg m ht.le]
    simp
  · intro r hr
    have h0 : N 0 = 0 := by simpa using hs 0 0 le_rfl
    exact ⟨(isOpen_lt hc continuous_const).measure_ne_zero lam ⟨0, by simpa [h0] using hr⟩,
      ((measure_mono fun x (hx : N x < r) => hx.le).trans_lt (hK r).measure_lt_top).ne⟩

theorem isCompact_matrixEntryAbsSum_sublevel (r : ℝ) :
    IsCompact {Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ | l1 Z ≤ r} := by
  have h : IsCompact (Set.univ.pi fun _ : Fin P ⊕ Fin Q => Set.univ.pi
      fun _ : Fin P ⊕ Fin Q => Metric.closedBall (0 : ℂ) r) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset (X := Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) h
    (isClosed_le continuous_matrixEntryAbsSum continuous_const) fun Z hZ i _ j _ => ?_
  rw [mem_closedBall_zero_iff]
  refine le_trans ?_ hZ
  exact (Finset.single_le_sum (f := fun j => ‖Z i j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖Z i j‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))

theorem ballU_props {lam : Measure (lieU P Q)} (h : IsOmegaLeb lam) :
    (∀ t r : ℝ, 0 < t → 0 < r → lam (ballU P Q (t * r)) =
      ENNReal.ofReal (t ^ Module.finrank ℝ (lieU P Q)) * lam (ballU P Q r)) ∧
    ∀ r : ℝ, 0 < r → lam (ballU P Q r) ≠ 0 ∧ lam (ballU P Q r) ≠ ⊤ := by
  haveI : BorelSpace (lieU P Q) := ⟨rfl⟩
  haveI := h.1
  refine addHaar_sublevel lam (fun X => l1 (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))
    (continuous_matrixEntryAbsSum.comp continuous_subtype_val) (fun t x ht => ?_) fun r => ?_
  · simp only [l1, Finset.mul_sum, SetLike.val_smul, Matrix.smul_apply, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ht]
  · exact (Submodule.closed_of_finiteDimensional
      (lieU P Q)).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_matrixEntryAbsSum_sublevel r)

theorem tanBall_props :
    (∀ t r : ℝ, 0 < t → 0 < r → (volume : Measure (ℝ × Sp P Q)) {x | tanGauge x < t * r} =
      ENNReal.ofReal (t ^ Module.finrank ℝ (ℝ × Sp P Q)) * volume {x : ℝ × Sp P Q | tanGauge x < r}) ∧
    ∀ r : ℝ, 0 < r → (volume : Measure (ℝ × Sp P Q)) {x | tanGauge x < r} ≠ 0 ∧
      (volume : Measure (ℝ × Sp P Q)) {x | tanGauge x < r} ≠ ⊤ := by
  haveI : (volume : Measure (ℝ × Sp P Q)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  refine addHaar_sublevel volume tanGauge continuous_tanGauge (fun t x ht => ?_) fun r => ?_
  · simp only [tanGauge, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul, abs_of_nonneg ht,
      Pi.smul_apply, norm_smul, Real.norm_eq_abs, ← Finset.mul_sum]
    ring
  · refine (isCompact_closedBall (0 : ℝ × Sp P Q) |r|).of_isClosed_subset
      (isClosed_le continuous_tanGauge continuous_const) fun x hx => ?_
    have hx : |x.1| + 2 * ∑ i, ‖x.2 i‖ ≤ r := hx
    have h1 : 0 ≤ ∑ i, ‖x.2 i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have h2 := abs_nonneg x.1
    have h3 := le_abs_self r
    rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff, pi_norm_le_iff_of_nonneg (abs_nonneg r)]
    refine ⟨by rw [Real.norm_eq_abs]; linarith, fun i => ?_⟩
    have := Finset.single_le_sum (f := fun i => ‖x.2 i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)
    linarith

theorem tendsto_gauge {μ : Measure (UpqT P Q)} {c : ℝ≥0∞} (hc : c ≠ ⊤) (h : OmegaDensity μ c)
    {lam : Measure (lieU P Q)} (hl : IsOmegaLeb lam) :
    Tendsto (fun r : ℝ => μ {g | gauge g < r} / lam (ballU P Q r)) (𝓝[>] 0) (𝓝 c) := by
  obtain ⟨lam', h1, h2⟩ := h
  obtain rfl := GlobalTheory.CompactDualUnique.isOmegaLeb_unique h1 hl
  refine tendsto_div_of_squeeze (F := fun r => μ (expBall P Q r)) hc (ballU_props hl).1 h2
    fun t ht => ?_
  filter_upwards [GlobalTheory.T.unitaryExpLieBall_comparable_entryGauge P Q t ht] with r hr using ⟨measure_mono hr.1, measure_mono hr.2⟩

theorem tendsto_fib (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (he : SignCompat e)
    {fib : ℝ → Measure (Sp P Q)} (hf : IsDxDq fib) :
    Tendsto (fun r : ℝ => fib (sg (e none)) {y | ptGauge e y < r} /
      (volume : Measure (ℝ × Sp P' Q')) {x | tanGauge x < r}) (𝓝[>] 0)
      (𝓝 ((2 : ℝ≥0∞) ^ (P' + Q'))) := by
  refine tendsto_div_of_squeeze (F := fun r => (2 : ℝ≥0∞) ^ (P' + Q') *
    (volume : Measure (ℝ × Sp P' Q')) {x | tanGauge x < r}) (by simp) tanBall_props.1 ?_
    fun t ht => ?_
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [mul_div_assoc, ENNReal.div_self (tanBall_props.2 r hr).1 (tanBall_props.2 r hr).2, mul_one]
  · filter_upwards [GlobalTheory.T.quadricPointGauge_polarCoordinates_compare_tangentGauge P Q P' Q' e t ht, Ioo_mem_nhdsGT one_pos] with r hr hr1
    rw [GlobalTheory.T.hermitianNormFibreMeasure_eq_polar_coordinates P Q P' Q' e he fib hf _
      (isOpen_lt (continuous_ptGauge e) continuous_const).measurableSet fun y hy h0 => ?_]
    · refine ⟨mul_le_mul_right (measure_mono fun u hu => ?_) _,
        mul_le_mul_right (measure_mono fun u hu => (hr u hu.1).2 hu.2) _⟩
      have h1 : u.1 ∈ Set.Ioo (-Real.pi) Real.pi := by
        have h2 : |u.1| + 2 * ∑ i, ‖u.2 i‖ < t⁻¹ * r := hu
        have h3 : 0 ≤ ∑ i, ‖u.2 i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
        have h4 : t⁻¹ * r ≤ 1 :=
          mul_le_one₀ (inv_le_one_of_one_le₀ ht.le) hr1.1.le hr1.2.le
        have h5 := Real.pi_gt_three
        exact abs_lt.1 (by linarith)
      exact ⟨h1, (hr u h1).1 hu⟩
    · have h2 : ‖y (e none) - 1‖ + 2 * ∑ i, ‖y (e (some i))‖ < r := hy
      have h3 : 0 ≤ ∑ i, ‖y (e (some i))‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      rw [h0, zero_sub, norm_neg, norm_one] at h2
      linarith [hr1.2]

theorem ptGauge_act_le (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (g : UpqT P Q) :
    ptGauge e (act g (baseVec e)) ≤ 2 * gauge g := by
  have h1 : ∀ i, act g (baseVec e) i = UpqT.mat g i (e none) := fun i => by
    simp [act, baseVec]
  have h2 : ∑ i, ‖(UpqT.mat g - 1) i (e none)‖ ≤ gauge g :=
    Finset.sum_le_sum fun i _ => Finset.single_le_sum (f := fun j => ‖(UpqT.mat g - 1) i j‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
  rw [← e.sum_comp, Fintype.sum_option] at h2
  simp only [Matrix.sub_apply, Matrix.one_apply, e.injective.eq_iff, if_true, reduceCtorEq,
    if_false, sub_zero] at h2
  simp only [ptGauge, h1]
  linarith [norm_nonneg (UpqT.mat g (e none) (e none) - 1)]

theorem const_mul_density (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (he : SignCompat e)
    {fib : ℝ → Measure (Sp P Q)} (hf : IsDxDq fib) (j : UpqT P' Q' →* UpqT P Q)
    (hj : IsBlockEmb e j) (hjc : Continuous j) (hjs : ∀ g, act (j g) (baseVec e) = baseVec e)
    {μ : Measure (UpqT P Q)} {μ' : Measure (UpqT P' Q')} [μ'.IsHaarMeasure]
    {a a' : ℝ≥0∞} (ha : a ≠ ⊤) (ha' : a' ≠ ⊤) (h : OmegaDensity μ a) (h' : OmegaDensity μ' a')
    (κ : ℝ≥0) (hκ : ∀ s : Sp P Q → UpqT P Q, IsSection (sg (e none)) (baseVec e) s →
      ∀ f : UpqT P Q → ℝ≥0∞, Measurable f →
        ∫⁻ y, (∫⁻ g', f (s y * j g') ∂μ') ∂(fib (sg (e none))) = κ * ∫⁻ g, f g ∂μ) :
    κ * a = a' := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  obtain ⟨i1', i2', i3', i4', i5', -⟩ := GlobalTheory.UpqTopology.upq_lcsc P' Q'
  haveI : BorelSpace (lieU P' Q') := ⟨rfl⟩
  obtain ⟨σ, hσ, hσe⟩ := GlobalTheory.T.exists_tangent_borelSection_quadric P Q P' Q' e
  have ⟨lam, hl, _⟩ := h
  have ⟨lam', hl', _⟩ := h'
  haveI := hl'.1
  haveI : LocallyCompactSpace (Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin P' ⊕ Fin Q') → (Fin P' ⊕ Fin Q') → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P' ⊕ Fin Q') → (Fin P' ⊕ Fin Q') → ℂ))
  haveI : LocallyCompactSpace (lieU P' Q') :=
    (Submodule.closed_of_finiteDimensional (lieU P' Q')).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (lieU P' Q') :=
    TopologicalSpace.Subtype.secondCountableTopology _
  set ν := fib (sg (e none)) with hν
  haveI : IsFiniteMeasureOnCompacts ν := (GlobalTheory.T.hermitianNormFibreMeasure_finite_invariant P Q fib _ hf (sg_ne_zero _)).1
  haveI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  have h1 := GlobalTheory.T.tendsto_sublevel_density_prod_measure _ _ _ _ ν volume μ' lam' (ptGauge e) tanGauge gauge
    (fun X => l1 (X : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ)) _ a'
    (continuous_ptGauge e).measurable continuous_tanGauge.measurable continuous_gauge.measurable
    (continuous_matrixEntryAbsSum.comp continuous_subtype_val).measurable (ptGauge_nonneg e) tanGauge_nonneg
    (fun _ => weightAbsEntrySum_nonneg _) (fun _ => weightAbsEntrySum_nonneg _) (by simp) ha' tanBall_props.2
    (ballU_props hl').2 (tendsto_fib e he hf) (tendsto_gauge ha' h' hl')
  have h20 : (2 : ℝ≥0∞) ^ (P' + Q') ≠ 0 := by simp
  have h2t : (2 : ℝ≥0∞) ^ (P' + Q') ≠ ⊤ := by simp
  have h2 : Tendsto (fun r : ℝ => (ν.prod μ') {p | ptGauge e p.1 + gauge p.2 < r} /
      lam (ballU P Q r)) (𝓝[>] 0) (𝓝 a') := by
    have h3 := ENNReal.Tendsto.const_mul (a := ((2 : ℝ≥0∞) ^ (P' + Q'))⁻¹) h1
      (Or.inr (ENNReal.inv_ne_top.2 h20))
    rw [← mul_assoc, ENNReal.inv_mul_cancel h20 h2t, one_mul] at h3
    refine h3.congr fun r => ?_
    rw [GlobalTheory.T.unitaryLie_volume_ball_split_basis_vector P Q P' Q' e he lam lam' hl hl' r, div_eq_mul_inv, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inl h20) (Or.inl h2t)]
    ring
  have hm : Measurable fun p : Sp P Q × UpqT P' Q' => σ p.1 * j p.2 :=
    (hσ.1.comp measurable_fst).mul (hjc.measurable.comp measurable_snd)
  have hS : ∀ r : ℝ, MeasurableSet {g : UpqT P Q | gauge g < r} := fun r =>
    (isOpen_lt continuous_gauge continuous_const).measurableSet
  have h4 : ∀ r : ℝ, (ν.prod μ') {p | gauge (σ p.1 * j p.2) < r} = κ * μ {g | gauge g < r} := by
    intro r
    rw [← lintegral_indicator_one (hS r), ← hκ σ hσ _ (measurable_one.indicator (hS r)),
      ← lintegral_indicator_one (s := {p : Sp P Q × UpqT P' Q' | gauge (σ p.1 * j p.2) < r})
        (hm (hS r))]
    exact lintegral_prod _ (measurable_one.indicator (hm (hS r))).aemeasurable
  have hae : ∀ᵐ p ∂(ν.prod μ'), qf p.1 = sg (e none) :=
    (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := μ')).ae (GlobalTheory.RealPlaceCompare.ae_qf hf _)
  have h5 : Tendsto (fun r : ℝ => (ν.prod μ') {p | gauge (σ p.1 * j p.2) < r} /
      lam (ballU P Q r)) (𝓝[>] 0) (𝓝 a') := by
    refine tendsto_div_of_squeeze ha' (ballU_props hl).1 h2 fun t ht => ?_
    obtain ⟨δ, hδ, H⟩ := GlobalTheory.T.quadricPointGauge_section_mul_block_compare P Q P' Q' e j hj t ht
    have ht0 : 0 < t := by linarith
    filter_upwards [Ioo_mem_nhdsGT (show 0 < min δ 1 / 2 by positivity)] with r hr
    have hr1 : 2 * r < δ := by linarith [hr.2, min_le_left δ 1]
    have hr2 : 2 * r < 1 := by linarith [hr.2, min_le_right δ 1]
    have key : ∀ p : Sp P Q × UpqT P' Q', qf p.1 = sg (e none) → ptGauge e p.1 < 2 * r →
        ptGauge e p.1 + gauge p.2 ≤ t * gauge (σ p.1 * j p.2) ∧
          gauge (σ p.1 * j p.2) ≤ t * (ptGauge e p.1 + gauge p.2) := fun p hp hlt => by
      have hne : p.1 (e none) ≠ -1 := fun h0 => by
        have h6 : ‖p.1 (e none) - 1‖ + 2 * ∑ i, ‖p.1 (e (some i))‖ < 2 * r := hlt
        have h7 : 0 ≤ ∑ i, ‖p.1 (e (some i))‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
        have h8 : ‖(-1 - 1 : ℂ)‖ = 2 := by norm_num
        rw [h0, h8] at h6
        linarith
      exact H p.1 (σ p.1) (by linarith) (hσ.2 _ hp) (hσe _ hp hne).1 (hσe _ hp hne).2 p.2
    refine ⟨measure_mono_ae (hae.mono fun p hp hlt => ?_),
      measure_mono_ae (hae.mono fun p hp hlt => ?_)⟩
    · have hlt : ptGauge e p.1 + gauge p.2 < t⁻¹ * r := hlt
      have h6 : t⁻¹ * r ≤ r := mul_le_of_le_one_left hr.1.le (inv_le_one_of_one_le₀ ht.le)
      have h7 : 0 ≤ gauge p.2 := weightAbsEntrySum_nonneg _
      have h8 := (key p hp (by linarith [hr.1])).2
      exact h8.trans_lt ((lt_inv_mul_iff₀ ht0).1 hlt)
    · have hlt : gauge (σ p.1 * j p.2) < r := hlt
      have h6 := ptGauge_act_le e (σ p.1 * j p.2)
      rw [GlobalTheory.RealPlaceCompare.act_mul, hjs, hσ.2 _ hp] at h6
      exact (key p hp (by linarith)).1.trans_lt (mul_lt_mul_of_pos_left hlt ht0)
  have h6 := ENNReal.Tendsto.const_mul (a := (κ : ℝ≥0∞)) (tendsto_gauge ha h hl)
    (Or.inr ENNReal.coe_ne_top)
  refine tendsto_nhds_unique (h6.congr fun r => ?_) h5
  rw [h4, mul_div_assoc]

theorem formula_base (c : CDHaar) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
    (he : SignCompat e) {fib : ℝ → Measure (Sp P Q)} (hf : IsDxDq fib)
    (j : UpqT P' Q' →* UpqT P Q) (hj : IsBlockEmb e j) (hjc : IsClosedEmbedding j)
    (hjr : Set.range j = {g | act g (baseVec e) = baseVec e})
    {s : Sp P Q → UpqT P Q} (hs : IsSection (sg (e none)) (baseVec e) s)
    {f : UpqT P Q → ℝ≥0∞} (hfm : Measurable f) :
    ∫⁻ y, (∫⁻ g', f (s y * j g') ∂(c.cd P' Q')) ∂(fib (sg (e none))) =
      ENNReal.ofReal (cM (P + Q)) * ∫⁻ g, f g ∂(c.cd P Q) := by
  obtain ⟨a, ha0, hat, ha1, ha2⟩ := c.trick P Q
  obtain ⟨a', -, hat', ha1', ha2'⟩ := c.trick P' Q'
  haveI := c.haar P' Q'
  haveI := c.haar (P' + Q') 0
  haveI := c.prob (P' + Q')
  haveI := c.prob (P + Q)
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.invariant_measure_quadric_mul_haar_stabilizer P Q P' Q' _ _ j _ _ _ hjc hjr (GlobalTheory.T.hermitianNormFibreMeasure_finite_invariant P Q fib _ hf (sg_ne_zero _)).1
    (GlobalTheory.RealPlaceCompare.ae_qf hf _) (GlobalTheory.T.hermitianNormFibreMeasure_finite_invariant P Q fib _ hf (sg_ne_zero (e none))).2
    (c.haar P Q) (c.haar P' Q')
  have k1 := const_mul_density e he hf j hj hjc.continuous
    (fun g => (hjr ▸ Set.mem_range_self g : j g ∈ {g | act g (baseVec e) = baseVec e}))
    hat hat' ha1 ha1' κ hκ
  have hcard := card_eq e
  let e₀ : Option (Fin (P' + Q') ⊕ Fin 0) ≃ (Fin (P + Q) ⊕ Fin 0) :=
    Fintype.equivOfCardEq (by simp [hcard])
  have sg0 : ∀ {n : ℕ} (i : Fin n ⊕ Fin 0), sg i = 1 := fun i => by
    rcases i with i | i
    · rfl
    · exact i.elim0
  have he₀ : SignCompat e₀ := fun i => by rw [sg0, sg0]
  obtain ⟨j₀, hj₀, hjc₀, hjr₀⟩ := GlobalTheory.T.exists_unitaryBlockEmbedding_onto_stabiliser _ _ _ _ e₀ he₀
  obtain ⟨⟨fib₀, hf₀⟩, hmass⟩ := GlobalTheory.T.positiveDefiniteUnitSphereMass_proof (P + Q) (by omega)
  obtain ⟨κ₀, hκ₀⟩ := GlobalTheory.T.invariant_measure_quadric_mul_haar_stabilizer _ _ _ _ _ _ j₀ _ _ _ hjc₀ hjr₀
    (GlobalTheory.T.hermitianNormFibreMeasure_finite_invariant _ _ fib₀ _ hf₀ (sg_ne_zero _)).1
    (GlobalTheory.RealPlaceCompare.ae_qf hf₀ _) (GlobalTheory.T.hermitianNormFibreMeasure_finite_invariant _ _ fib₀ _ hf₀ (sg_ne_zero (e₀ none))).2
    (c.haar (P + Q) 0) (c.haar (P' + Q') 0)
  have k2 := const_mul_density e₀ he₀ hf₀ j₀ hj₀ hjc₀.continuous
    (fun g => (hjr₀ ▸ Set.mem_range_self g : j₀ g ∈ {g | act g (baseVec e₀) = baseVec e₀}))
    hat hat' ha2 ha2' κ₀ hκ₀
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.QuadricSection.exists_isSection _ _ _ _ (sg_ne_zero (e₀ none))
    (qf_baseVec e₀)
  have k3 := hκ₀ s₀ hs₀ (fun _ => 1) measurable_const
  simp only [lintegral_const, measure_univ, mul_one, one_mul, sg0, hmass fib₀ hf₀] at k3
  rw [hκ s hs f hfm, (ENNReal.mul_left_inj ha0 hat).1 (k1.trans k2.symm), k3]

theorem quotFormula (c : CDHaar) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
    (he : SignCompat e) : QuotFormula c P Q P' Q' (sg (e none)) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  obtain ⟨j₀, hj₀, hjc₀, hjr₀⟩ := GlobalTheory.T.exists_unitaryBlockEmbedding_onto_stabiliser _ _ _ _ e he
  intro x₀ hx₀
  constructor
  · obtain ⟨s₀, hs₀⟩ := GlobalTheory.QuadricSection.exists_isSection _ _ _ _ (sg_ne_zero (e none))
      (qf_baseVec e)
    obtain ⟨A, hA⟩ := GlobalTheory.T.exists_isOrthogonalComplementIsometryEmbedding_translate _ _ _ _ e he j₀ hj₀ (s₀ x₀)
    rw [hs₀.2 x₀ hx₀] at hA
    exact ⟨(A, _), hA⟩
  rintro ⟨A, j⟩ hA
  obtain ⟨g₀, hg₀, hj⟩ := GlobalTheory.T.orthogonalComplement_unitary_embedding_conj_block _ _ _ _ e he j₀ hj₀ x₀ A j hx₀ hA
  have hinv : act g₀⁻¹ x₀ = baseVec e := by
    rw [← hg₀, ← GlobalTheory.RealPlaceCompare.act_mul, inv_mul_cancel, GlobalTheory.RealPlaceCompare.act_one]
  refine ⟨?_, GlobalTheory.RealPlaceCompare.exists_isDxDq P Q, fun fib hf =>
    ⟨GlobalTheory.QuadricSection.exists_isSection _ _ _ _ (sg_ne_zero _) hx₀, fun s hs f hfm => ?_⟩⟩
  · ext g
    refine ⟨?_, fun hg => ?_⟩
    · rintro ⟨k, rfl⟩; exact (hA.2.2 k).1
    · obtain ⟨k, hk⟩ : g₀⁻¹ * g * g₀ ∈ Set.range j₀ := by
        rw [hjr₀]
        change act _ _ = _
        rw [GlobalTheory.RealPlaceCompare.act_mul, GlobalTheory.RealPlaceCompare.act_mul, hg₀, hg, hinv]
      exact ⟨k, by change j k = g; rw [hj, hk]; group⟩
  · haveI := c.haar P Q
    haveI := GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure P Q _ (c.haar P Q)
    have H := formula_base c e he hf j₀ hj₀ hjc₀ hjr₀ (s := fun y => s y * g₀)
      ⟨hs.1.mul_const g₀, fun y hy => by rw [GlobalTheory.RealPlaceCompare.act_mul, hg₀, hs.2 y hy]⟩
      (f := fun g => f (g * g₀⁻¹)) (hfm.comp (measurable_mul_const _))
    rw [lintegral_mul_right_eq_self] at H
    simp only [hj, ← mul_assoc]
    rw [H, ← mul_assoc, ENNReal.inv_mul_cancel (by simpa using cM_pos _) ENNReal.ofReal_ne_top,
      one_mul]

theorem compactDualQuotient : CompactDualQuotient := by
  intro c P Q
  constructor
  · let e : Option (Fin P ⊕ Fin Q) ≃ (Fin (P + 1) ⊕ Fin Q) :=
      { toFun := fun o => o.elim (Sum.inl 0) (Sum.map Fin.succ id)
        invFun := Sum.elim (fun i => Fin.cases none (fun k => some (Sum.inl k)) i)
          (fun i => some (Sum.inr i))
        left_inv := by rintro (_ | i | i) <;> simp
        right_inv := by
          rintro (i | i)
          · refine Fin.cases ?_ (fun k => ?_) i <;> simp
          · simp }
    exact quotFormula c e (by rintro (i | i) <;> rfl)
  · let e : Option (Fin P ⊕ Fin Q) ≃ (Fin P ⊕ Fin (Q + 1)) :=
      { toFun := fun o => o.elim (Sum.inr 0) (Sum.map id Fin.succ)
        invFun := Sum.elim (fun i => some (Sum.inl i))
          (fun i => Fin.cases none (fun k => some (Sum.inr k)) i)
        left_inv := by rintro (_ | i | i) <;> simp
        right_inv := by
          rintro (i | i)
          · simp
          · refine Fin.cases ?_ (fun k => ?_) i <;> simp }
    exact quotFormula c e (by rintro (i | i) <;> rfl)

end GlobalTheory.CompactDualQuot
