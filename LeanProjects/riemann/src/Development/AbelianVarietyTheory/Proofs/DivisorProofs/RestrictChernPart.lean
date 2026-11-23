import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Measure
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess bas wd wdb)
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts GlobalTheory.FinChart
open scoped ENNReal

namespace GlobalTheory.ChernMA

theorem cHess_eq_hessC {D : ℕ} {h : V D → ℝ} {z : Fin D → ℂ} (hf : ContDiffAt ℝ 2 h (toV D z)) :
    cHess D (fun v => (h v : ℂ)) (toV D z) = hessC (h ∘ toV D) z := by
  have h₁ : fderiv ℝ (h ∘ toV D) =
      fun w => (fderiv ℝ h (toV D w)).comp (toV D).toContinuousLinearMap :=
    funext fun _ => (toV D).comp_right_fderiv
  have hD := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have h₂ := ((hD.comp z (toV D).hasFDerivAt).clm_comp
    (hasFDerivAt_const (toV D).toContinuousLinearMap z)).fderiv
  set x := toV D z
  set H := fderiv ℝ (fderiv ℝ h) x
  have hH (a b : Fin D → ℂ) : fderiv ℝ (fderiv ℝ (h ∘ toV D)) z a b = H (toV D a) (toV D b) := by
    rw [h₁]
    erw [h₂]
    simp
  have hdiff := ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf
  set G : Fin D → V D → ℂ := fun k y => (2 : ℂ)⁻¹ *
    ((fderiv ℝ h y (bas D k) : ℂ) + Complex.I * (fderiv ℝ h y (Complex.I • bas D k) : ℂ))
  have hwdb : ∀ k, wdb D k (fun y => (h y : ℂ)) =ᶠ[𝓝 x] G k := by
    intro k
    filter_upwards [hdiff] with y hy
    simp only [wdb, G, ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply hy]
    ring
  have hGd : ∀ k e, fderiv ℝ (G k) x e =
      ((H e (bas D k) : ℂ) + Complex.I * (H e (Complex.I • bas D k) : ℂ)) / 2 := by
    intro k e
    have ha : ∀ b : V D, HasFDerivAt (fun y => ((fderiv ℝ h y b : ℝ) : ℂ))
        (Complex.ofRealCLM.comp ((fderiv ℝ h x).comp (0 : V D →L[ℝ] V D) + H.flip b)) x :=
      fun b => Complex.ofRealCLM.hasFDerivAt.comp x (hD.clm_apply (hasFDerivAt_const b x))
    have hG : HasFDerivAt (G k) _ x :=
      ((ha (bas D k)).add ((ha (Complex.I • bas D k)).const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
    rw [hG.fderiv]
    simp
    ring
  have e₁ (a : Fin D) : toV D (Pi.single a 1) = bas D a := rfl
  have e₂ (a : Fin D) : toV D (Complex.I • Pi.single a 1) = Complex.I • bas D a := rfl
  ext j l
  rw [cHess, Matrix.of_apply, wd, (hwdb l).fderiv_eq, hGd, hGd]
  simp only [hessC, hH, e₁, e₂]
  push_cast
  linear_combination (-(H (Complex.I • bas D j) (Complex.I • bas D l) : ℂ) / 4) * Complex.I_mul_I

theorem map_withDensity {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {m : Measure α}
    {s : α → β} (hs : AEMeasurable s m) {g : β → ℝ≥0∞} (hg : Measurable g) :
    (m.map s).withDensity g = (m.withDensity (g ∘ s)).map s := by
  ext T hT
  rw [Measure.map_apply_of_aemeasurable (hs.mono_ac (withDensity_absolutelyContinuous _ _)) hT,
    withDensity_apply _ hT, ← lintegral_indicator hT,
    lintegral_map' (hg.indicator hT).aemeasurable hs,
    withDensity_apply₀ _ (hs.nullMeasurableSet_preimage hT),
    ← lintegral_indicator₀ (hs.nullMeasurableSet_preimage hT)]
  rfl

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {B : LB Y} {φ : Weight p σ B} {A : FinHolAtlas D (CxPts p σ)}

theorem locDens_eq (h : φ.IsCInf) {c : AlgChart p σ D} {j : Fin A.n} (hc : A.chart j = c.finChart)
    {z : Fin D → ℂ} (hz : z ∈ c.finChart.target) :
    locDens A (fun _ => φ.locPot) j z = c.chernDens φ (c.finChart.symm z) := by
  have hy := c.finChart.map_target hz
  have hr : c.e (c.finChart.symm z) = toV D z := c.e.right_inv hz
  have hs := h.contDiffAt c hy (mem_pick φ.isLB _)
  rw [hr] at hs
  have e : (fun y' => φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y')) = fun v => 2⁻¹ *
      ((fun v => φ.φ (pick φ.isLB (c.finChart.symm z)) (c.e.symm v)) ∘ toV D) v :=
    funext fun _ => div_eq_inv_mul _ _
  rw [locDens, hc, maDens, ReciprocityTheory.AnForm.A.mdisc_const, e, hessC_const_mul', AlgChart.chernDens,
    AlgChart.hess, hr, cHess_eq_hessC hs, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow,
    Complex.re_ofReal_mul, div_pow, inv_pow]
  field_simp

variable [SecondCountableTopology (CxPts p σ)]

theorem restrict_chernPart (h : φ.IsCInf) (ε : ℤˣ) (c : AlgChart p σ D) :
    (φ.chernPart D ε).restrict c.finChart.source = ((volume.restrict c.finChart.target).withDensity
      fun z => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ (c.finChart.symm z))).map c.finChart.symm := by
  ext T hT
  have ht := c.finChart.open_target.measurableSet
  have hs : AEMeasurable c.finChart.symm (volume.restrict c.finChart.target) :=
    c.finChart.continuousOn_symm.aemeasurable ht
  have hp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin D → ℂ)) :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin D → ℂ)).symm
      (volume_preserving_ofLp_complex (Fin D))
  rw [Measure.restrict_apply hT, Weight.chernPart_apply h ε c
      (hT.inter c.finChart.open_source.measurableSet) inter_subset_right,
    Measure.map_apply_of_aemeasurable (hs.mono_ac (withDensity_absolutelyContinuous _ _)) hT,
    withDensity_apply', Measure.restrict_restrict' ht, inter_comm, AlgChart.finChart_source,
    c.e.image_source_inter_eq', ← hp.setLIntegral_comp_preimage_emb
      (MeasurableEquiv.measurableEmbedding _), inter_comm]
  rfl

variable [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]

omit [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] in

theorem chernPart_eq_sum (h : φ.IsCInf) (hA : IsAlgAtlas A) (P : ChartPartition A) (ε : ℤˣ) :
    φ.chernPart D ε = ∑ j, chartPartMeasure A P (fun _ => φ.locPot) (ε : ℤ) j := by
  have hm (j) : Measurable fun y => ENNReal.ofReal (P.χ j y) :=
    ENNReal.measurable_ofReal.comp (continuousOn_univ.1
      (((hA.smooth_iff hA.anRead).1 (P.smooth j)).continuousOn isOpen_univ)).measurable
  have hpot := ((Weight.isCInf_iff_isSmooth hA.anRead).1 h).isPotential hA
  have key (j) : chartPartMeasure A P (fun _ => φ.locPot) (ε : ℤ) j =
      (φ.chernPart D ε).withDensity fun y => ENNReal.ofReal (P.χ j y) := by
    obtain ⟨c, hc⟩ := hA j
    have ht := c.finChart.open_target.measurableSet
    have hs : AEMeasurable c.finChart.symm (volume.restrict c.finChart.target) :=
      c.finChart.continuousOn_symm.aemeasurable ht
    have e : (fun y => ENNReal.ofReal (P.χ j y)) =
        c.finChart.source.indicator fun y => ENNReal.ofReal (P.χ j y) := by
      refine (indicator_eq_self.2 fun y hy => hc ▸ P.tsupport_subset j (subset_tsupport _ ?_)).symm
      exact fun h0 => hy (by simp [h0])
    have hd : AEMeasurable (fun z => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ (c.finChart.symm z)))
        (volume.restrict c.finChart.target) := by
      have := locDensCont A _ (fun _ => hpot) j
      rw [hc] at this
      exact (((this.congr fun z hz => (locDens_eq h hc hz).symm).aemeasurable ht).const_mul
        _).ennreal_ofReal
    rw [e, withDensity_indicator c.finChart.open_source.measurableSet, restrict_chernPart h,
      map_withDensity (hs.mono_ac (withDensity_absolutelyContinuous _ _)) (hm j),
      ← withDensity_mul₀ hd ((hm j).comp_aemeasurable hs), chartPartMeasure]
    simp only [hc]
    refine congrArg _ (withDensity_congr_ae (ae_restrict_of_forall_mem ht fun z hz => ?_))
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [locDens_eq h hc hz, mul_left_comm, ENNReal.ofReal_mul (P.nonneg _ _), mul_comm]
  ext T hT
  simp only [key, Measure.coe_finsetSum, Finset.sum_apply, withDensity_apply _ hT]
  rw [← lintegral_finsetSum _ fun j _ => hm j, ← setLIntegral_one]
  refine lintegral_congr fun y => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => P.nonneg j y, P.sum_eq_one, ENNReal.ofReal_one]

theorem chernInt_eq_mInt (h : φ.IsCInf) (hA : IsAlgAtlas A) {f : CxPts p σ → ℝ}
    (hf : Continuous f) : φ.chernInt D univ f = mInt A (fun _ => φ.locPot) f := by
  have hΦ : ∀ _ : Fin D, IsPotential A φ.locPot := fun _ =>
    ((Weight.isCInf_iff_isSmooth hA.anRead).1 h).isPotential hA
  have hi := mIntegrableCont A _ hΦ f hf
  set P := (existsPartition A).some
  have h1 := fun s j => integral_chartPartMeasure A P _ hΦ s j f hf.measurable hi
  have h2 (s : ℝ) (j) : IntegrableOn (fun y => f ((A.chart j).symm y) * max (s * (P.χ j
      ((A.chart j).symm y) * locDens A (fun _ => φ.locPot) j y)) 0) (A.chart j).target := by
    obtain ⟨hK, hKT, h0⟩ := chart_weight_compact A P (fun _ => φ.locPot) j
    have hχ : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target :=
      (P.smooth j j).continuousOn.mono fun y hy => ⟨hy, mem_univ _⟩
    refine ((((hf.comp_continuousOn (A.chart j).continuousOn_symm).mul ((continuousOn_const.mul
      (hχ.mul (locDensCont A _ hΦ j))).sup continuousOn_const)).mono hKT).integrableOn_compact
      hK).of_forall_sdiff_eq_zero (A.chart j).open_target.measurableSet fun y hy => ?_
    simp [h0 y hy.1 hy.2]
  rw [Weight.chernInt, Measure.restrict_univ, Measure.restrict_univ, chernPart_eq_sum h hA P,
    chernPart_eq_sum h hA P, integral_finsetSum_measure fun j _ => (h1 _ j).1,
    integral_finsetSum_measure fun j _ => (h1 _ j).1, ← Finset.sum_sub_distrib, mInt,
    dif_pos (existsPartition A), integralWith]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(h1 _ j).2, (h1 _ j).2, ← integral_sub (h2 _ j) (h2 _ j)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg]
  rw [one_mul, neg_one_mul, ← mul_sub, max_zero_sub_max_neg_zero_eq_self]
  ring

end GlobalTheory.ChernMA
