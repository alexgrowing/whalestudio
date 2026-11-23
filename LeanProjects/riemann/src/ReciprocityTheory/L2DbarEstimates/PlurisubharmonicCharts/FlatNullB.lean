import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatNullA

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal

noncomputable section

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}

theorem fn_mu_compl (hN : EXTNullStatement n) (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) :
    A.mu (A.Mset w0 s De)ᶜ = 0 := by
  apply measure_null_of_locally_null
  intro x _
  have hxs : x ∈ (A.chart (A.pick x)).source := A.mem_pick x
  have hxt : (A.chart (A.pick x)) x ∈ (A.chart (A.pick x)).target := (A.chart (A.pick x)).map_source hxs
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (A.chart (A.pick x)).open_target _ hxt
  have hGd : DifferentiableOn ℂ (fnG A w0 s De (A.pick x)) (Metric.ball ((A.chart (A.pick x)) x) r) :=
    (fn_diffG A hD (A.pick x)).mono hball
  have hO1 : IsOpen ((A.chart (A.pick x)).source ∩
      (A.chart (A.pick x)) ⁻¹' Metric.ball ((A.chart (A.pick x)) x) r) :=
    (A.chart (A.pick x)).continuousOn.isOpen_inter_preimage (A.chart (A.pick x)).open_source Metric.isOpen_ball
  have hB2 : IsOpen (Metric.ball ((A.chart (A.pick x)) x) r ∩ fnG A w0 s De (A.pick x) ⁻¹' {0}ᶜ) :=
    hGd.continuousOn.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
  have hO2 : IsOpen ((A.chart (A.pick x)).source ∩ (A.chart (A.pick x)) ⁻¹'
      (Metric.ball ((A.chart (A.pick x)) x) r ∩ fnG A w0 s De (A.pick x) ⁻¹' {0}ᶜ)) :=
    (A.chart (A.pick x)).continuousOn.isOpen_inter_preimage (A.chart (A.pick x)).open_source hB2
  have hne : ∃ y ∈ Metric.ball ((A.chart (A.pick x)) x) r, fnG A w0 s De (A.pick x) y ≠ 0 := by
    obtain ⟨y, ⟨hys, hyB⟩, hyM⟩ := (fn_dense A hD hF).inter_open_nonempty _ hO1
      ⟨x, hxs, Metric.mem_ball_self hr⟩
    refine ⟨(A.chart (A.pick x)) y, hyB, ?_⟩
    rw [fn_G_ne_iff A hD ((A.chart (A.pick x)).map_source hys), (A.chart (A.pick x)).left_inv hys]
    exact hyM
  have hZ : volume (Metric.ball ((A.chart (A.pick x)) x) r ∩ {v | fnG A w0 s De (A.pick x) v = 0}) = 0 :=
    hN _ _ _ hGd hne
  set T := ((A.chart (A.pick x)).source ∩
      (A.chart (A.pick x)) ⁻¹' Metric.ball ((A.chart (A.pick x)) x) r) \
      ((A.chart (A.pick x)).source ∩ (A.chart (A.pick x)) ⁻¹'
        (Metric.ball ((A.chart (A.pick x)) x) r ∩ fnG A w0 s De (A.pick x) ⁻¹' {0}ᶜ)) with hTdef
  have hTm : MeasurableSet T := hO1.measurableSet.diff hO2.measurableSet
  have hvol : volume ((A.chart (A.pick x)) '' T) = 0 := by
    refine measure_mono_null ?_ hZ
    rintro v ⟨y, hyT, rfl⟩
    refine ⟨hyT.1.2, ?_⟩
    by_contra hG
    exact hyT.2 ⟨hyT.1.1, hyT.1.2, hG⟩
  have hTnull : A.mu T = 0 := by
    rw [A.mu_chart (A.pick x) T hTm (fun y hy => hy.1.1)]
    first
      | exact setLIntegral_measure_zero _ _ hvol
      | simp [Measure.restrict_eq_zero.2 hvol]
  refine ⟨(A.Mset w0 s De)ᶜ ∩ ((A.chart (A.pick x)).source ∩
      (A.chart (A.pick x)) ⁻¹' Metric.ball ((A.chart (A.pick x)) x) r),
    inter_mem_nhdsWithin _ (hO1.mem_nhds ⟨hxs, Metric.mem_ball_self hr⟩), ?_⟩
  refine measure_mono_null ?_ hTnull
  rintro y ⟨hyM, hys, hyB⟩
  refine ⟨⟨hys, hyB⟩, ?_⟩
  rintro ⟨_, _, hG⟩
  apply hyM
  have := (fn_G_ne_iff A hD ((A.chart (A.pick x)).map_source hys)).1 hG
  rwa [(A.chart (A.pick x)).left_inv hys] at this

def fnRho (i : ι) (v : V n) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v)))

theorem fn_symm_aemeas (i : ι) :
    AEMeasurable (A.chart i).symm (volume.restrict (A.chart i).target) :=
  (A.chart i).continuousOn_symm.aemeasurable (A.chart i).open_target.measurableSet

theorem fn_rho_aemeas (i : ι) : AEMeasurable (fnRho A i) (volume.restrict (A.chart i).target) := by
  have h : ContinuousOn (fnRho A i) (A.chart i).target :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap i).continuousOn)
  exact h.aemeasurable (A.chart i).open_target.measurableSet

theorem fn_map (i : ι) :
    Measure.map (A.chart i).symm ((volume.restrict (A.chart i).target).withDensity (fnRho A i)) =
      A.mu.restrict (A.chart i).source := by
  have hsymm : AEMeasurable (A.chart i).symm
      ((volume.restrict (A.chart i).target).withDensity (fnRho A i)) :=
    (fn_symm_aemeas A i).mono_ac (withDensity_absolutelyContinuous _ _)
  refine Measure.ext fun t ht => ?_
  rw [Measure.map_apply_of_aemeasurable hsymm ht, withDensity_apply' _ _,
    Measure.restrict_restrict' (A.chart i).open_target.measurableSet, Measure.restrict_apply ht,
    A.mu_chart i _ (ht.inter (A.chart i).open_source.measurableSet) Set.inter_subset_right,
    Set.inter_comm t (A.chart i).source, (A.chart i).image_source_inter_eq', Set.inter_comm]
  rfl

theorem fn_lint (i : ι) {φ : Y → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ x in (A.chart i).source, φ x ∂A.mu =
      ∫⁻ v in (A.chart i).target, fnRho A i v * φ ((A.chart i).symm v) := by
  have hsymm : AEMeasurable (A.chart i).symm
      ((volume.restrict (A.chart i).target).withDensity (fnRho A i)) :=
    (fn_symm_aemeas A i).mono_ac (withDensity_absolutelyContinuous _ _)
  rw [← fn_map A i, lintegral_map' hφ.aemeasurable hsymm]
  exact lintegral_withDensity_eq_lintegral_mul₀ (fn_rho_aemeas A i)
    (hφ.comp_aemeasurable (fn_symm_aemeas A i))
theorem fn_contOn_sec {la : La} {U : Set Y} {F : ι → Y → ℂ} (hFs : A.IsSecOn la U F) (i : ι) :
    ContinuousOn (F i) ((A.chart i).source ∩ U) := by
  have h := (hFs.1 i).continuousOn.comp ((A.chart i).continuousOn.mono Set.inter_subset_left)
    (fun x hx => ⟨(A.chart i).map_source hx.1, by
      show (A.chart i).symm ((A.chart i) x) ∈ U
      rw [(A.chart i).left_inv hx.1]
      exact hx.2⟩)
  refine h.congr fun x hx => ?_
  simp [Function.comp, (A.chart i).left_inv hx.1]

theorem fn_contOn_ph (la : La) (i : ι) : ContinuousOn (A.ph la i) (A.chart i).source := by
  have h := (A.smooth_ph la i).continuousOn.comp (A.chart i).continuousOn
    (fun x hx => (A.chart i).map_source hx)
  refine h.congr fun x hx => ?_
  simp [Function.comp, (A.chart i).left_inv hx]

theorem fn_nsq_eq {la : La} {U : Set Y} {F : ι → Y → ℂ} (hFs : A.IsSecOn la U F) {i : ι} {x : Y}
    (hxs : x ∈ (A.chart i).source) (hxU : x ∈ U) :
    ‖F i x‖ ^ 2 * Real.exp (-A.ph la i x) = A.nsq la F x := by
  unfold WeightedAtlas.nsq
  have hj : x ∈ (A.chart (A.pick x)).source := A.mem_pick x
  have hg : 0 < ‖A.g la i (A.pick x) x‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (A.g_ne la i (A.pick x) x hxs hj)) 2
  rw [hFs.2 i (A.pick x) x hxU hxs hj, A.ph_trans la i (A.pick x) x hxs hj,
    show -(A.ph la i x - Real.log (‖A.g la i (A.pick x) x‖ ^ 2)) =
      Real.log (‖A.g la i (A.pick x) x‖ ^ 2) + -A.ph la i x by ring,
    Real.exp_add, Real.exp_log hg, norm_mul]
  ring

theorem fn_loc (hD : A.D0 L w w0 s) {la : La} {F : ι → Y → ℂ}
    (hFs : A.IsSecOn la (A.Mset w0 s De) F)
    (hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal (A.nsq la F x) ∂A.mu < ⊤)
    (i : ι) {v : V n} (hv : v ∈ (A.chart i).target) :
    ∃ r > 0, Metric.ball v r ⊆ (A.chart i).target ∧
      ∫⁻ u in Metric.ball v r \ {u | fnG A w0 s De i u = 0},
        ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2) < ⊤ := by
  classical
  obtain ⟨U, hU, hfin⟩ := hloc ((A.chart i).symm v)
  have hc1 : ContinuousAt (A.ph A.kap i ∘ (A.chart i).symm) v :=
    (A.smooth_ph A.kap i).continuousOn.continuousAt ((A.chart i).open_target.mem_nhds hv)
  have hc2 : ContinuousAt (A.ph la i ∘ (A.chart i).symm) v :=
    (A.smooth_ph la i).continuousOn.continuousAt ((A.chart i).open_target.mem_nhds hv)
  have he1 : ∀ᶠ u in 𝓝 v, u ∈ (A.chart i).target := (A.chart i).open_target.mem_nhds hv
  have he2 : ∀ᶠ u in 𝓝 v, (A.chart i).symm u ∈ U := ((A.chart i).continuousAt_symm hv).preimage_mem_nhds hU
  have hev := he1.and (he2.and
      ((hc1.eventually (Metric.ball_mem_nhds _ one_pos)).and
        (hc2.eventually (Metric.ball_mem_nhds _ one_pos))))
  obtain ⟨r, hr, hrP⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hball : Metric.ball v r ⊆ (A.chart i).target := fun u hu => (hrP u hu).1
  refine ⟨r, hr, hball, ?_⟩
  have hGc : ContinuousOn (fnG A w0 s De i) (Metric.ball v r) :=
    ((fn_diffG A hD i).mono hball).continuousOn
  have hSo : IsOpen (Metric.ball v r \ {u | fnG A w0 s De i u = 0}) :=
    hGc.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
  have hSM : ∀ u ∈ Metric.ball v r \ {u | fnG A w0 s De i u = 0},
      u ∈ (A.chart i).target ∧ (A.chart i).symm u ∈ A.Mset w0 s De := fun u hu =>
    ⟨hball hu.1, (fn_G_ne_iff A hD (hball hu.1)).1 hu.2⟩
  have hFS : ContinuousOn (F i ∘ (A.chart i).symm) (Metric.ball v r \ {u | fnG A w0 s De i u = 0}) :=
    (hFs.1 i).continuousOn.mono fun u hu => hSM u hu
  set W := (A.chart i).source ∩ (A.chart i) ⁻¹' (Metric.ball v r \ {u | fnG A w0 s De i u = 0}) with hWdef
  have hWo : IsOpen W := (A.chart i).continuousOn.isOpen_inter_preimage (A.chart i).open_source hSo
  have hWM : ∀ y ∈ W, y ∈ A.Mset w0 s De ∧ y ∈ U := by
    intro y hy
    have h := (hSM _ hy.2)
    rw [(A.chart i).left_inv hy.1] at h
    have h2 := (hrP _ hy.2.1).2.1
    rw [(A.chart i).left_inv hy.1] at h2
    exact ⟨h.2, h2⟩
  have hFW : ContinuousOn (F i) W := by
    refine (hFS.comp ((A.chart i).continuousOn.mono (fun y hy => hy.1)) (fun y hy => hy.2)).congr ?_
    intro y hy
    simp [Function.comp, (A.chart i).left_inv hy.1]
  have hphW : ContinuousOn (A.ph la i) W := (fn_contOn_ph A la i).mono fun y hy => hy.1
  have hgc : ContinuousOn (fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y))) W :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (((continuous_norm.comp_continuousOn hFW).pow 2).mul (Real.continuous_exp.comp_continuousOn hphW.neg))
  have hφm : Measurable (W.indicator fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y))) := by
    rw [← Set.piecewise_eq_indicator]
    exact hgc.measurable_piecewise continuousOn_const hWo.measurableSet
  have hlint := fn_lint A i hφm
  have hY : ∫⁻ x in (A.chart i).source,
      W.indicator (fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y))) x ∂A.mu < ⊤ := by
    refine lt_of_le_of_lt ?_ hfin
    calc ∫⁻ x in (A.chart i).source,
          W.indicator (fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y))) x ∂A.mu
        ≤ ∫⁻ x, W.indicator (fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y))) x ∂A.mu :=
          lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ∫⁻ x in W, ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x)) ∂A.mu :=
          lintegral_indicator hWo.measurableSet _
      _ ≤ ∫⁻ x in W, ENNReal.ofReal (A.nsq la F x) ∂A.mu := by
          refine setLIntegral_mono' hWo.measurableSet fun x hx => le_of_eq ?_
          rw [fn_nsq_eq A hFs hx.1 (hWM x hx).1]
      _ ≤ ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal (A.nsq la F x) ∂A.mu :=
          lintegral_mono_set fun x hx => ⟨(hWM x hx).2, (hWM x hx).1⟩
  rw [hlint] at hY
  set a := Real.exp (-(A.ph la i ((A.chart i).symm v)) - 1) with ha
  set b := Real.exp (A.ph A.kap i ((A.chart i).symm v) - 1) with hb
  have ha0 : 0 < a := Real.exp_pos _
  have hb0 : 0 < b := Real.exp_pos _
  have hpt : ∀ u ∈ Metric.ball v r \ {u | fnG A w0 s De i u = 0},
      ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2) ≤ ENNReal.ofReal (1 / (a * b)) *
        (fnRho A i u * W.indicator (fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y)))
          ((A.chart i).symm u)) := by
    intro u hu
    have huW : (A.chart i).symm u ∈ W :=
      ⟨(A.chart i).map_target (hball hu.1), by rw [Set.mem_preimage, (A.chart i).right_inv (hball hu.1)]; exact hu⟩
    rw [Set.indicator_of_mem huW]
    have h3 := (hrP u hu.1).2.2.1
    have h4 := (hrP u hu.1).2.2.2
    rw [Real.dist_eq] at h3 h4
    have h3' := abs_lt.1 h3
    have h4' := abs_lt.1 h4
    simp only [Function.comp] at h3' h4'
    have hA : a ≤ Real.exp (-A.ph la i ((A.chart i).symm u)) := Real.exp_le_exp.2 (by linarith)
    have hB : b ≤ Real.exp (A.ph A.kap i ((A.chart i).symm u)) := Real.exp_le_exp.2 (by linarith)
    have hX : 0 ≤ ‖F i ((A.chart i).symm u)‖ ^ 2 := by positivity
    show ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2) ≤ ENNReal.ofReal (1 / (a * b)) *
      (ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm u))) *
        ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2 * Real.exp (-A.ph la i ((A.chart i).symm u))))
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hab : a * b ≤ Real.exp (-A.ph la i ((A.chart i).symm u)) * Real.exp (A.ph A.kap i ((A.chart i).symm u)) :=
      mul_le_mul hA hB hb0.le (Real.exp_pos _).le
    have key : ‖F i ((A.chart i).symm u)‖ ^ 2 * (a * b) ≤
        ‖F i ((A.chart i).symm u)‖ ^ 2 * (Real.exp (-A.ph la i ((A.chart i).symm u)) *
          Real.exp (A.ph A.kap i ((A.chart i).symm u))) := mul_le_mul_of_nonneg_left hab hX
    calc ‖F i ((A.chart i).symm u)‖ ^ 2
        = 1 / (a * b) * (‖F i ((A.chart i).symm u)‖ ^ 2 * (a * b)) := by field_simp
      _ ≤ 1 / (a * b) * (‖F i ((A.chart i).symm u)‖ ^ 2 * (Real.exp (-A.ph la i ((A.chart i).symm u)) *
          Real.exp (A.ph A.kap i ((A.chart i).symm u)))) := mul_le_mul_of_nonneg_left key (by positivity)
      _ = 1 / (a * b) * (Real.exp (A.ph A.kap i ((A.chart i).symm u)) *
          (‖F i ((A.chart i).symm u)‖ ^ 2 * Real.exp (-A.ph la i ((A.chart i).symm u)))) := by ring
  calc ∫⁻ u in Metric.ball v r \ {u | fnG A w0 s De i u = 0}, ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2)
      ≤ ∫⁻ u in Metric.ball v r \ {u | fnG A w0 s De i u = 0}, ENNReal.ofReal (1 / (a * b)) *
        (fnRho A i u * W.indicator (fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y)))
          ((A.chart i).symm u)) := setLIntegral_mono' hSo.measurableSet hpt
    _ = ENNReal.ofReal (1 / (a * b)) * ∫⁻ u in Metric.ball v r \ {u | fnG A w0 s De i u = 0},
        fnRho A i u * W.indicator (fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y)))
          ((A.chart i).symm u) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (1 / (a * b)) * ∫⁻ u in (A.chart i).target,
        fnRho A i u * W.indicator (fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y)))
          ((A.chart i).symm u) := by
          gcongr
          first
            | exact fun u (hu : u ∈ Metric.ball v r \ {u | fnG A w0 s De i u = 0}) => hball hu.1
            | exact Measure.restrict_mono (fun u (hu : u ∈ Metric.ball v r \ {u | fnG A w0 s De i u = 0}) => hball hu.1) le_rfl
            | exact lintegral_mono_set fun u (hu : u ∈ Metric.ball v r \ {u | fnG A w0 s De i u = 0}) => hball hu.1
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hY
theorem fn_sub_closure (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (i : ι) {O : Set (V n)}
    (hO : IsOpen O) (hOt : O ⊆ (A.chart i).target) :
    O ⊆ closure (O ∩ {u | fnG A w0 s De i u ≠ 0}) := by
  intro u hu
  rw [mem_closure_iff]
  intro W hW huW
  have hWO : IsOpen ((A.chart i).source ∩ (A.chart i) ⁻¹' (W ∩ O)) :=
    (A.chart i).continuousOn.isOpen_inter_preimage (A.chart i).open_source (hW.inter hO)
  have hut : u ∈ (A.chart i).target := hOt hu
  obtain ⟨y, ⟨hys, hyWO⟩, hyM⟩ := (fn_dense A hD hF).inter_open_nonempty _ hWO
    ⟨(A.chart i).symm u, (A.chart i).map_target hut, by
      rw [Set.mem_preimage, (A.chart i).right_inv hut]; exact ⟨huW, hu⟩⟩
  refine ⟨(A.chart i) y, hyWO.1, hyWO.2, ?_⟩
  show fnG A w0 s De i ((A.chart i) y) ≠ 0
  rw [fn_G_ne_iff A hD ((A.chart i).map_source hys), (A.chart i).left_inv hys]
  exact hyM

theorem fn_ext (hE : EXTStatement n) (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (la : La) (F : ι → Y → ℂ) (hFs : A.IsSecOn la (A.Mset w0 s De) F)
    (hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal (A.nsq la F x) ∂A.mu < ⊤) :
    ∃ G : ι → Y → ℂ, A.IsSec la G ∧
      ∀ i y, y ∈ A.Mset w0 s De → y ∈ (A.chart i).source → G i y = F i y := by
  classical
  have hext : ∀ i, ∃ g : V n → ℂ, DifferentiableOn ℂ g (A.chart i).target ∧
      ∀ u ∈ (A.chart i).target, fnG A w0 s De i u ≠ 0 → g u = F i ((A.chart i).symm u) := by
    intro i
    have hloc' : ∀ u ∈ (A.chart i).target, ∃ r > 0, Metric.ball u r ⊆ (A.chart i).target ∧
        ∃ U : V n → ℂ, DifferentiableOn ℂ U (Metric.ball u r) ∧
          Set.EqOn U (F i ∘ (A.chart i).symm) (Metric.ball u r \ {y | fnG A w0 s De i y = 0}) := by
      intro u hu
      obtain ⟨r, hr, hball, hint⟩ := fn_loc A hD hFs hloc i hu
      have hd1 : DifferentiableOn ℂ (fnG A w0 s De i) (Metric.ball u r) := (fn_diffG A hD i).mono hball
      have hd2 : DifferentiableOn ℂ (F i ∘ (A.chart i).symm) (Metric.ball u r \ {y | fnG A w0 s De i y = 0}) :=
        (hFs.1 i).mono fun y hy => ⟨hball hy.1, (fn_G_ne_iff A hD (hball hy.1)).1 hy.2⟩
      obtain ⟨U, hU1, hU2⟩ := hE u r (fnG A w0 s De i) (F i ∘ (A.chart i).symm) hd1 hd2 hint
      exact ⟨r, hr, hball, U, hU1, hU2⟩
    choose! r hr hball U hU1 hU2 using hloc'

    have hagree : ∀ u₀ ∈ (A.chart i).target, ∀ u ∈ (A.chart i).target,
        ∀ w ∈ Metric.ball u (r u) ∩ Metric.ball u₀ (r u₀), U u w = U u₀ w := by
      intro u₀ hu₀ u hu w hw
      have hO : IsOpen (Metric.ball u (r u) ∩ Metric.ball u₀ (r u₀)) := Metric.isOpen_ball.inter Metric.isOpen_ball
      have hOt : Metric.ball u (r u) ∩ Metric.ball u₀ (r u₀) ⊆ (A.chart i).target :=
        fun x hx => hball u hu hx.1
      have hcl := fn_sub_closure A hD hF i hO hOt
      refine Set.EqOn.of_subset_closure ?_ ((hU1 u hu).continuousOn.mono fun x hx => hx.1)
        ((hU1 u₀ hu₀).continuousOn.mono fun x hx => hx.2) Set.inter_subset_left hcl hw
      intro x hx
      rw [hU2 u hu ⟨hx.1.1, hx.2⟩, hU2 u₀ hu₀ ⟨hx.1.2, hx.2⟩]
    refine ⟨fun u => U u u, ?_, ?_⟩
    · intro u₀ hu₀
      have hd : DifferentiableAt ℂ (U u₀) u₀ :=
        (hU1 u₀ hu₀).differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hr u₀ hu₀)))
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hr u₀ hu₀))] with u hu
      have hut : u ∈ (A.chart i).target := hball u₀ hu₀ hu
      exact hagree u₀ hu₀ u hut u ⟨Metric.mem_ball_self (hr u hut), hu⟩
    · intro u hu hG
      exact hU2 u hu ⟨Metric.mem_ball_self (hr u hu), hG⟩
  choose g hg1 hg2 using hext
  have hGF : ∀ i y, y ∈ A.Mset w0 s De → y ∈ (A.chart i).source → g i ((A.chart i) y) = F i y := by
    intro i y hyM hys
    have ht := (A.chart i).map_source hys
    rw [hg2 i _ ht (by rw [fn_G_ne_iff A hD ht, (A.chart i).left_inv hys]; exact hyM),
      (A.chart i).left_inv hys]
  have hGc : ∀ i, ContinuousOn (fun y => g i ((A.chart i) y)) (A.chart i).source := fun i =>
    (hg1 i).continuousOn.comp (A.chart i).continuousOn fun y hy => (A.chart i).map_source hy
  refine ⟨fun i y => g i ((A.chart i) y), ⟨fun i => ?_, fun i j y _ hyi hyj => ?_⟩, hGF⟩
  · refine ((hg1 i).mono Set.inter_subset_left).congr ?_
    intro u hu
    simp [Function.comp, (A.chart i).right_inv hu.1]
  · have hVo : IsOpen ((A.chart i).source ∩ (A.chart j).source) :=
      (A.chart i).open_source.inter (A.chart j).open_source
    have hgc : ContinuousOn (A.g la i j) ((A.chart i).source ∩ (A.chart j).source) := by
      refine ((A.holo_g la i j).continuousOn.comp ((A.chart i).continuousOn.mono Set.inter_subset_left) ?_).congr ?_
      · intro x hx
        exact ⟨(A.chart i).map_source hx.1, by rw [Set.mem_preimage, (A.chart i).left_inv hx.1]; exact hx.2⟩
      · intro x hx
        simp [Function.comp, (A.chart i).left_inv hx.1]
    have hcl := (fn_dense A hD hF).open_subset_closure_inter hVo
    refine Set.EqOn.of_subset_closure (f := fun y => g i ((A.chart i) y))
      (g := fun y => A.g la i j y * g j ((A.chart j) y)) ?_
      ((hGc i).mono Set.inter_subset_left) (hgc.mul ((hGc j).mono Set.inter_subset_right))
      Set.inter_subset_left hcl ⟨hyi, hyj⟩
    intro x hx
    simp only
    rw [hGF i x hx.2 hx.1.1, hGF j x hx.2 hx.1.2]
    exact hFs.2 i j x hx.2 hx.1.1 hx.1.2

end

end ReciprocityTheory.L2DbarEstimates.Y
