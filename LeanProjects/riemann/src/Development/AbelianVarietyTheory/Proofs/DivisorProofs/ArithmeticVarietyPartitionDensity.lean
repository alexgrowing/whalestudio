import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDensityExists

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical ENNReal

namespace GlobalTheory.MixDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {w ρ : AlgChart p σ D → CxPts p σ → ℝ}

theorem IsDens.setLIntegral_part [SecondCountableTopology (CxPts p σ)] (h : IsDens w)
    (c : AlgChart p σ D) {A : Set (CxPts p σ)} (hA : MeasurableSet A) (hc : A ⊆ c.e.source)
    {f : CxPts p σ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in A, f y ∂(part w) =
      ∫⁻ v in c.e '' A, ENNReal.ofReal (w c (c.e.symm v)) * f (c.e.symm v) := by
  have hS := ChartGlue.measurableSet_image c.e hA hc
  have hSt : c.e '' A ⊆ c.e.target := (Set.image_mono hc).trans c.e.image_source_eq_target.subset
  have hsym : AEMeasurable c.e.symm (volume.restrict (c.e '' A)) :=
    (c.e.continuousOn_symm.mono hSt).aemeasurable hS
  have hφ : AEMeasurable (fun v => ENNReal.ofReal (w c (c.e.symm v)))
      (volume.restrict (c.e '' A)) :=
    (((h.2 c).mono hSt).aemeasurable hS).ennreal_ofReal
  have hsym' := hsym.mono_ac (withDensity_absolutelyContinuous (volume.restrict (c.e '' A))
    fun v => ENNReal.ofReal (w c (c.e.symm v)))
  have key : (part w).restrict A = Measure.map c.e.symm
      ((volume.restrict (c.e '' A)).withDensity fun v => ENNReal.ofReal (w c (c.e.symm v))) := by
    ext B hB
    rw [Measure.restrict_apply hB, h.part_apply c (hB.inter hA) (Set.inter_subset_right.trans hc),
      Measure.map_apply_of_aemeasurable hsym' hB, withDensity_apply',
      Measure.restrict_restrict' hS]
    congr 2
    ext v
    constructor
    · rintro ⟨y, ⟨hyB, hyA⟩, rfl⟩
      exact ⟨by rwa [Set.mem_preimage, c.e.left_inv (hc hyA)], ⟨y, hyA, rfl⟩⟩
    · rintro ⟨hv, ⟨y, hyA, rfl⟩⟩
      rw [Set.mem_preimage, c.e.left_inv (hc hyA)] at hv
      exact ⟨y, ⟨hv, hyA⟩, rfl⟩
  rw [key, lintegral_map' hf.aemeasurable hsym']
  exact lintegral_withDensity_eq_lintegral_mul₀ hφ (hf.comp_aemeasurable hsym)

theorem IsDens.isFiniteMeasure_part [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    [SecondCountableTopology (CxPts p σ)] (h : IsDens w)
    (cov : ∀ y, ∃ c : AlgChart p σ D, y ∈ c.e.source) : IsFiniteMeasure (part w) := by
  have hfin : ∀ y, (part w).FiniteAtFilter (𝓝 y) := fun y => by
    obtain ⟨c, hy⟩ := cov y
    obtain ⟨ε, hε, hεt⟩ := Metric.isOpen_iff.1 c.e.open_target _ (c.e.map_source hy)
    set B := Metric.closedBall (c.e y) (ε / 2) with hBdef
    have hBt : B ⊆ c.e.target := (Metric.closedBall_subset_ball (by linarith)).trans hεt
    set T := c.e.symm '' B with hTdef
    have hTc : IsCompact T :=
      (isCompact_closedBall _ _).image_of_continuousOn (c.e.continuousOn_symm.mono hBt)
    have hTs : T ⊆ c.e.source := by
      rintro _ ⟨v, hv, rfl⟩; exact c.e.map_target (hBt hv)
    have hTB : c.e '' T = B := by
      rw [hTdef, Set.image_image]
      exact (Set.image_congr fun v hv => c.e.right_inv (hBt hv)).trans (Set.image_id' B)
    refine ⟨T, ?_, ?_⟩
    · refine mem_of_superset ((c.e.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds
        ⟨hy, Metric.mem_ball_self (half_pos hε)⟩) fun z hz => ⟨c.e z, ?_, c.e.left_inv hz.1⟩
      exact Metric.ball_subset_closedBall hz.2
    · rw [h.part_apply c hTc.isClosed.measurableSet hTs, hTB]
      exact (((h.2 c).mono hBt).integrableOn_compact (isCompact_closedBall _ _)).lintegral_lt_top
  refine ⟨?_⟩
  simpa using isCompact_univ.measure_lt_top_of_nhdsWithin fun y _ =>
    (hfin y).filter_mono nhdsWithin_le_nhds

theorem IsDens.exists_quotient (hw : IsDens w) (hpos : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, 0 < w c y)
    (cov : ∀ y, ∃ c : AlgChart p σ D, y ∈ c.e.source) (hρ : IsDens ρ) :
    ∃ g : CxPts p σ → ℝ, Continuous g ∧ ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source,
      ρ c y = g y * w c y := by
  choose pick hpick using cov
  have hval : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source,
      ρ c y = ρ (pick y) y / w (pick y) y * w c y := fun c y hy => by
    have hne := (hpos (pick y) y (hpick y)).ne'
    rw [hρ.1 c (pick y) y hy (hpick y), hw.1 c (pick y) y hy (hpick y)]
    field_simp
  refine ⟨fun y => ρ (pick y) y / w (pick y) y, continuous_iff_continuousAt.2 fun y => ?_, hval⟩
  have hcont : ∀ τ : AlgChart p σ D → CxPts p σ → ℝ, IsDens τ →
      ContinuousOn (τ (pick y)) (pick y).e.source := fun τ hτ =>
    ((hτ.2 (pick y)).comp (pick y).e.continuousOn (pick y).e.mapsTo).congr fun z hz => by
      simp [(pick y).e.left_inv hz]
  have ho := (pick y).e.open_source.mem_nhds (hpick y)
  refine (((hcont ρ hρ).continuousAt ho).div ((hcont w hw).continuousAt ho)
    (hpos _ y (hpick y)).ne').congr ?_
  filter_upwards [ho] with z hz
  rw [Pi.div_apply, hval (pick y) z hz, mul_div_assoc, div_self (hpos _ z hz).ne', mul_one]

theorem IsDens.part_eq_withDensity [SecondCountableTopology (CxPts p σ)] (hw : IsDens w)
    (hpos : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, 0 < w c y)
    (cov : ∀ y, ∃ c : AlgChart p σ D, y ∈ c.e.source) {g : CxPts p σ → ℝ} (hg : Continuous g)
    (hρ : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ρ c y = g y * w c y) :
    part ρ = (part w).withDensity fun y => ENNReal.ofReal (g y) := by
  have hd : IsDens ρ := (hw.mul hg).congr hρ
  refine ChartGlue.ext_of_cover (fun c : AlgChart p σ D => c.e.source) (fun c => c.e.open_source)
    cov fun c A hA hc => ?_
  rw [hd.part_apply c hA hc, withDensity_apply _ hA,
    hw.setLIntegral_part c hA hc hg.measurable.ennreal_ofReal]
  refine setLIntegral_congr_fun (ChartGlue.measurableSet_image c.e hA hc) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [c.e.left_inv (hc hy)]
  rw [hρ c y (hc hy), ENNReal.ofReal_mul' (hpos c y (hc hy)).le, mul_comm]

theorem IsDens.total_eq_integral [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    [SecondCountableTopology (CxPts p σ)] (hw : IsDens w)
    (hpos : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, 0 < w c y)
    (cov : ∀ y, ∃ c : AlgChart p σ D, y ∈ c.e.source) {g : CxPts p σ → ℝ} (hg : Continuous g)
    (hρ : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ρ c y = g y * w c y) :
    total ρ = ∫ y, g y ∂(part w) := by
  haveI := hw.isFiniteMeasure_part cov
  have hI : Integrable g (part w) :=
    integrableOn_univ.1 (hg.continuousOn.integrableOn_compact isCompact_univ)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI, total,
    hw.part_eq_withDensity hpos cov hg hρ,
    hw.part_eq_withDensity (ρ := fun c y => -ρ c y) (g := fun y => -g y) hpos cov hg.neg
      fun c y hy => by rw [hρ c y hy, neg_mul],
    withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

theorem exists_isDens_pos [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    (hR : Nonempty (AnRead p σ D)) : ∃ w : AlgChart p σ D → CxPts p σ → ℝ,
      IsDens w ∧ ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, 0 < w c y := by
  obtain ⟨R⟩ := hR
  obtain ⟨s, hs⟩ := R.exists_finite
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate (X := CxPts p σ) (ι := s) isClosed_univ
    (fun i => (R.chart i.1).e.source) (fun i => (R.chart i.1).e.open_source)
    (fun y _ => by
      obtain ⟨i, hi, hy⟩ := hs y
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hy⟩)
  have hsrc : ∀ (i : s) (y : CxPts p σ), f i y ≠ 0 → y ∈ (R.chart i.1).e.source := fun i y h =>
    hf i (subset_tsupport _ h)
  refine ⟨fun c y => ∑ i : s, f i y * ‖ChartGlue.transDet c.e (R.chart i.1).e y‖ ^ 2,
    ⟨fun c c' y hy hy' => ?_, fun c => ?_⟩, fun c y hy => ?_⟩
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : f i y = 0
    · simp [h]
    · rw [CurveDens.transDet_trans_chart c c' _ hy hy' (hsrc i y h), norm_mul, mul_pow]
      ring
  · refine continuousOn_finset_sum _ fun i _ => ?_
    have hg : ContinuousOn (fun y => f i y * ‖ChartGlue.transDet c.e (R.chart i.1).e y‖ ^ 2)
        c.e.source := fun y hy => by
      refine ContinuousAt.continuousWithinAt ?_
      by_cases h : y ∈ tsupport (f i)
      · exact (f i).continuous.continuousAt.mul
          ((CurveDens.continuousAt_transDet_chart c _ hy (hf i h)).norm.pow 2)
      · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 h] with z hz
        rw [hz, Pi.zero_apply, zero_mul]
    exact hg.comp c.e.continuousOn_symm fun v hv => c.e.map_target hv
  · obtain ⟨i, hi⟩ := f.exists_pos (Set.mem_univ y)
    refine Finset.sum_pos' (fun j _ => mul_nonneg (f.nonneg j y) (sq_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos hi (pow_pos (norm_pos_iff.2 ?_) 2)⟩
    exact CurveDens.transDet_chart_ne_zero c _ hy (hsrc i y hi.ne')

theorem exists_refMeasure : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ D) → ∃ (ν : Measure (CxPts p σ)) (w : AlgChart p σ D → CxPts p σ → ℝ), IsFiniteMeasure ν ∧ ν = part w ∧ IsDens w ∧ (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, 0 < w c y) ∧ (∀ ρ : AlgChart p σ D → CxPts p σ → ℝ, IsDens ρ → ∃ g : CxPts p σ → ℝ, Continuous g ∧ ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ρ c y = g y * w c y) ∧ ∀ (ρ : AlgChart p σ D → CxPts p σ → ℝ) (g : CxPts p σ → ℝ), Continuous g → (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ρ c y = g y * w c y) → part ρ = ν.withDensity (fun y => ENNReal.ofReal (g y)) ∧ total ρ = ∫ y, g y ∂ν := by
  intro k _ X p σ D _ _ _ hR
  obtain ⟨w, hw, hpos⟩ := exists_isDens_pos hR
  obtain ⟨R⟩ := hR
  have cov : ∀ y, ∃ c : AlgChart p σ D, y ∈ c.e.source := fun y =>
    let ⟨i, hi⟩ := R.cover y
    ⟨R.chart i, hi⟩
  exact ⟨part w, w, hw.isFiniteMeasure_part cov, rfl, hw, hpos,
    fun ρ hρ => hw.exists_quotient hpos cov hρ, fun ρ g hg hρ =>
      ⟨hw.part_eq_withDensity hpos cov hg hρ, hw.total_eq_integral hpos cov hg hρ⟩⟩

end GlobalTheory.MixDens
