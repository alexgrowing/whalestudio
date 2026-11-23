import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedOfDivisors
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ChernWeilLine
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace GlobalTheory.ChernWeilLine

theorem lintegral_toV_preimage {D : ℕ} (g : V D → ℝ≥0∞) (U : Set (V D)) :
    ∫⁻ z in GlobalTheory.FinChart.toV D ⁻¹' U, g (GlobalTheory.FinChart.toV D z) = ∫⁻ v in U, g v := by
  have hp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin D → ℂ)) :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin D → ℂ)).symm
      (volume_preserving_ofLp_complex (Fin D))
  exact hp.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _) g U

theorem glueMeas_real_sub_eq_mInt : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {σ : F →+* ℂ} {Z : Type} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] (A : FinHolAtlas Y.dim Z) (h : Z ≃ₜ Pts Y σ), (∀ j, ∃ c : GlobalTheory.AlgChart Y.str σ Y.dim, A.chart j = h.transOpenPartialHomeomorph c.finChart) → ∀ (Φ : Fin Y.dim → LocPot Z), (∀ i, IsPotential A (Φ i)) → ∀ (d : GlobalTheory.AlgChart Y.str σ Y.dim → Pts Y σ → ℝ), (∀ c c' y, y ∈ c.e.source → y ∈ c'.e.source → d c y = ‖transDet c.e c'.e y‖ ^ 2 * d c' y) → (∀ j (c : GlobalTheory.AlgChart Y.str σ Y.dim), A.chart j = h.transOpenPartialHomeomorph c.finChart → ∀ z ∈ (A.chart j).target, locDens A Φ j z = d c (c.finChart.symm z)) → (glueMeas (fun c : GlobalTheory.AlgChart Y.str σ Y.dim => c.e) fun c y => ENNReal.ofReal (((1 : ℤˣ) : ℤ) * d c y)).real Set.univ - (glueMeas (fun c : GlobalTheory.AlgChart Y.str σ Y.dim => c.e) fun c y => ENNReal.ofReal (((-1 : ℤˣ) : ℤ) * d c y)).real Set.univ = mInt A Φ (fun _ => 1) := by
  intro F _ _ Y σ Z _ _ _ A h hA Φ hΦ d hd hl
  have := CxPts.secondCountableTopology_of_isProjOver σ Y.isProjOver
  borelize Z
  have hρ (ε : ℤˣ) (c c' : GlobalTheory.AlgChart Y.str σ Y.dim) (y : Pts Y σ) (hy : y ∈ c.e.source)
      (hy' : y ∈ c'.e.source) : ENNReal.ofReal (((ε : ℤ) : ℝ) * d c y) =
        ENNReal.ofReal (‖transDet c.e c'.e y‖ ^ 2) * ENNReal.ofReal (((ε : ℤ) : ℝ) * d c' y) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _), hd c c' y hy hy']
    ring_nf
  have hglue (ε : ℤˣ) (c : GlobalTheory.AlgChart Y.str σ Y.dim) {S : Set (Pts Y σ)} (hS : MeasurableSet S)
      (hsub : S ⊆ c.e.source) :
      glueMeas (fun c : GlobalTheory.AlgChart Y.str σ Y.dim => c.e)
        (fun c y => ENNReal.ofReal (((ε : ℤ) : ℝ) * d c y)) S =
      chartMeas c.e (fun y => ENNReal.ofReal (((ε : ℤ) : ℝ) * d c y)) S :=
    glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => hρ ε c c' y hy hy') c hS hsub
  set μ : ℤˣ → Measure Z := fun ε => (glueMeas (fun c : GlobalTheory.AlgChart Y.str σ Y.dim => c.e)
    (fun c y => ENNReal.ofReal (((ε : ℤ) : ℝ) * d c y))).map h.symm with hμ
  have hres (ε : ℤˣ) (j : Fin A.n) (c : GlobalTheory.AlgChart Y.str σ Y.dim)
      (hc : A.chart j = h.transOpenPartialHomeomorph c.finChart) :
      (μ ε).restrict (A.chart j).source = ((volume.restrict (A.chart j).target).withDensity
        fun z => ENNReal.ofReal (((ε : ℤ) : ℝ) * d c (c.finChart.symm z))).map (A.chart j).symm := by
    ext T hT
    have ht := (A.chart j).open_target.measurableSet
    have hs : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
      (A.chart j).continuousOn_symm.aemeasurable ht
    have hS : MeasurableSet (h.symm ⁻¹' T ∩ c.e.source) :=
      (h.symm.continuous.measurable hT).inter c.e.open_source.measurableSet
    rw [Measure.restrict_apply hT, hμ, Measure.map_apply h.symm.continuous.measurable
        (hT.inter (A.chart j).open_source.measurableSet),
      Measure.map_apply_of_aemeasurable (hs.mono_ac (withDensity_absolutelyContinuous _ _)) hT,
      withDensity_apply', Measure.restrict_restrict' ht]
    have e1 : h.symm ⁻¹' (T ∩ (A.chart j).source) = h.symm ⁻¹' T ∩ c.e.source := by
      rw [hc, Homeomorph.transOpenPartialHomeomorph_source, AlgChart.finChart_source]
      ext y; simp
    rw [e1, hglue ε c hS inter_subset_right, chartMeas_apply_of_subset _ _ hS inter_subset_right,
      inter_comm, c.e.image_source_inter_eq']
    have e2 : (A.chart j).symm ⁻¹' T ∩ (A.chart j).target =
        GlobalTheory.FinChart.toV Y.dim ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' (h.symm ⁻¹' T)) := by
      rw [hc, Homeomorph.transOpenPartialHomeomorph_symm_apply,
        Homeomorph.transOpenPartialHomeomorph_target, AlgChart.finChart_target]
      ext z
      simp only [mem_inter_iff, mem_preimage, Function.comp_apply, AlgChart.finChart_symm_apply]
      tauto
    rw [e2, ← lintegral_toV_preimage]
    rfl
  set P := (existsPartition A).some with hP
  have hm (j : Fin A.n) : Measurable fun y => ENNReal.ofReal (P.χ j y) := by
    have h1 := (P.smooth j j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at h1
    have h2 : ContinuousOn (P.χ j) (A.chart j).source := by
      refine (h1.comp (A.chart j).continuousOn (fun y hy => (A.chart j).map_source hy)).congr ?_
      intro y hy
      simp [(A.chart j).left_inv hy]
    have h3 : Continuous (P.χ j) :=
      h2.continuous_of_tsupport_subset (A.chart j).open_source (P.tsupport_subset j)
    exact ENNReal.measurable_ofReal.comp h3.measurable
  have key (ε : ℤˣ) (j : Fin A.n) : chartPartMeasure A P Φ ((ε : ℤ) : ℝ) j =
      (μ ε).withDensity fun y => ENNReal.ofReal (P.χ j y) := by
    obtain ⟨c, hc⟩ := hA j
    have ht := (A.chart j).open_target.measurableSet
    have hs : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
      (A.chart j).continuousOn_symm.aemeasurable ht
    have e : (fun y => ENNReal.ofReal (P.χ j y)) =
        (A.chart j).source.indicator fun y => ENNReal.ofReal (P.χ j y) := by
      refine (indicator_eq_self.2 fun y hy => P.tsupport_subset j (subset_tsupport _ ?_)).symm
      exact fun h0 => hy (by simp [h0])
    have hdm : AEMeasurable (fun z => ENNReal.ofReal (((ε : ℤ) : ℝ) * d c (c.finChart.symm z)))
        (volume.restrict (A.chart j).target) := by
      have := locDensCont A Φ hΦ j
      exact (((this.congr fun z hz => (hl j c hc z hz).symm).aemeasurable ht).const_mul
        _).ennreal_ofReal
    rw [e, withDensity_indicator (A.chart j).open_source.measurableSet, hres ε j c hc,
      GlobalTheory.ChernMA.map_withDensity (hs.mono_ac (withDensity_absolutelyContinuous _ _)) (hm j),
      ← withDensity_mul₀ hdm ((hm j).comp_aemeasurable hs), chartPartMeasure]
    refine congrArg _ (withDensity_congr_ae (ae_restrict_of_forall_mem ht fun z hz => ?_))
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [hl j c hc z hz, mul_left_comm, ENNReal.ofReal_mul (P.nonneg _ _), mul_comm]
  have hsum (ε : ℤˣ) : μ ε = ∑ j, chartPartMeasure A P Φ ((ε : ℤ) : ℝ) j := by
    ext T hT
    simp only [key, Measure.coe_finsetSum, Finset.sum_apply, withDensity_apply _ hT]
    rw [← lintegral_finsetSum _ fun j _ => hm j, ← setLIntegral_one]
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => P.nonneg j y, P.sum_eq_one, ENNReal.ofReal_one]
  have hi := mIntegrableCont A Φ hΦ (fun _ => (1 : ℝ)) continuous_const
  have h1 := fun (s : ℝ) j => integral_chartPartMeasure A P Φ hΦ s j (fun _ => (1 : ℝ))
    measurable_const hi
  have h2 (s : ℝ) (j : Fin A.n) : IntegrableOn (fun y => (fun _ => (1 : ℝ)) ((A.chart j).symm y) *
      max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0) (A.chart j).target := by
    obtain ⟨hK, hKT, h0⟩ := chart_weight_compact A P Φ j
    have hχ : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target :=
      (P.smooth j j).continuousOn.mono fun y hy => ⟨hy, mem_univ _⟩
    refine (((continuousOn_const.mul ((continuousOn_const.mul
      (hχ.mul (locDensCont A Φ hΦ j))).sup continuousOn_const)).mono hKT).integrableOn_compact
      hK).of_forall_sdiff_eq_zero (A.chart j).open_target.measurableSet fun y hy => ?_
    simp [h0 y hy.1 hy.2]
  have hreal (ε : ℤˣ) : (glueMeas (fun c : GlobalTheory.AlgChart Y.str σ Y.dim => c.e)
      fun c y => ENNReal.ofReal (((ε : ℤ) : ℝ) * d c y)).real univ =
      ∑ j, ∫ x, (fun _ => (1 : ℝ)) x ∂chartPartMeasure A P Φ ((ε : ℤ) : ℝ) j := by
    rw [← integral_finsetSum_measure fun j _ => (h1 _ j).1, ← hsum ε, integral_const, smul_eq_mul,
      mul_one, hμ, Measure.real, Measure.real, Measure.map_apply h.symm.continuous.measurable
      MeasurableSet.univ, preimage_univ]
  rw [hreal 1, hreal (-1), ← Finset.sum_sub_distrib, mInt, dif_pos (existsPartition A), integralWith]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(h1 _ j).2, (h1 _ j).2, ← integral_sub (h2 _ j) (h2 _ j)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_mul, neg_one_mul,
    mul_one]
  rw [max_zero_sub_max_neg_zero_eq_self]

end GlobalTheory.ChernWeilLine
