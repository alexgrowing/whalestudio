import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNsqCanonicalAddChartPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableNsqExtendAndPsiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAtSimpleZeroOfWeightedSqIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenAtlasSectionNonvanishingSetAndMemIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ExtensionAcrossDenseNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureComplNonvanishingSetEqZeroOfDenseStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.extension_values_at_zeros : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ hS : (A.zeroSet s).Finite, (∀ P ∈ A.zeroSet s, jacAt A s P ≠ 0) → (∀ y, A.sqn L s y ≤ 1) → ∀ δ : ℝ, 0 < δ → ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → ∀ (Ω : Set Y) (h : ι → Y → ℂ) (T : ℝ) (θ : ℝ → ℝ), (IsOpen Ω ∧ A.IsSecOn (A.kap + E) Ω h ∧ (∀ i y, y ∉ Ω → h i y = 0)) → A.zeroSet s ⊆ Ω → IsCut T θ → ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu < ⊤ → ∀ F : ι → Y → ℂ, A.IsSecOn (A.kap + E) (nz A τ) F → ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu < ⊤ → ∃ G : ι → Y → ℂ, A.IsSec (A.kap + E) G ∧ (∀ i y, y ∈ nz A τ → y ∈ (A.chart i).source → G i y = F i y) ∧ ∀ P ∈ A.zeroSet s, G (A.pick P) P = h (A.pick P) P := by
  intro n Y _ _ _ _ _ _ ι La _ A hn E L s hs hS hjac hle δ hδ Λ τ hτ hdense Ω h T θ hΩ hSΩ hθ hhint F hF hint
  obtain ⟨hΩo, hhsec, hh0⟩ := hΩ
  have hUo : IsOpen (nz A τ) := (GlobalTheory.T.isOpen_atlasSectionNonvanishingSet_and_mem_iff n Y ι La A Λ τ hτ).1
  have hmeas := GlobalTheory.T.measurable_nsq_and_psi_of_isSecOn n Y ι La A (A.kap + E) Ω h hΩo hhsec hh0
  have hψm : Measurable (psi A L s) := hmeas.2 L s hs
  have hψle : ∀ y, psi A L s y ≤ 0 := fun y => by
    unfold psi
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n)
      (Real.log_nonpos (A.sqn_nonneg L s y) (hle y))
  set c0 : ℝ := 1 / (1 + (T + 1) ^ 2) with hc0def
  have hc0 : 0 < c0 := by positivity
  have hwT : ∀ x, c0 ≤ wT T x := fun x => by
    unfold wT
    apply one_div_le_one_div_of_le (by positivity)
    linarith [min_le_right (x ^ 2) ((T + 1) ^ 2)]
  have hwe : ∀ y, c0 * Real.exp (-psi A L s y) ≤
      wT T (δ * psi A L s y) * Real.exp (-psi A L s y) := fun y =>
    mul_le_mul_of_nonneg_right (hwT _) (Real.exp_pos _).le
  have hexψ : ∀ y, 1 ≤ Real.exp (-psi A L s y) := fun y => Real.one_le_exp (by linarith [hψle y])
  set X : ι → Y → ℂ := fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x with hXdef

  have hpt : ∀ y, A.nsq (A.kap + E) F y ≤ 2 * A.nsq (A.kap + E) h y +
      (2 / c0) * (A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) := by
    intro y
    have hθ01 := hθ.2.2.2.1 (δ * psi A L s y)
    have key : A.nsq (A.kap + E) F y ≤ 2 * A.nsq (A.kap + E) h y + 2 * A.nsq (A.kap + E) X y := by
      simp only [WeightedAtlas.nsq, X]
      set t := θ (δ * psi A L s y)
      set a := F (A.pick y) y
      set b := h (A.pick y) y
      have n1 : ‖(t : ℂ) * b‖ ≤ ‖b‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ01.1]
        exact mul_le_of_le_one_left (norm_nonneg _) hθ01.2
      have ha : ‖a‖ ^ 2 ≤ 2 * ‖b‖ ^ 2 + 2 * ‖(t : ℂ) * b - a‖ ^ 2 := by
        have e1 : a = (t : ℂ) * b - ((t : ℂ) * b - a) := by ring
        have n2 : ‖a‖ ≤ ‖(t : ℂ) * b‖ + ‖(t : ℂ) * b - a‖ := by
          conv_lhs => rw [e1]
          exact norm_sub_le _ _
        have n3 : 0 ≤ ‖(t : ℂ) * b‖ := norm_nonneg _
        have n4 : 0 ≤ ‖(t : ℂ) * b - a‖ := norm_nonneg _
        nlinarith [sq_nonneg (‖(t : ℂ) * b‖ - ‖(t : ℂ) * b - a‖), norm_nonneg a]
      have hex := Real.exp_pos (-A.ph (A.kap + E) (A.pick y) y)
      nlinarith
    have hX0 : 0 ≤ A.nsq (A.kap + E) X y := A.nsq_nonneg _ _ _
    have hq : A.nsq (A.kap + E) X y ≤
        A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)) / c0 := by
      rw [le_div_iff₀ hc0]
      have := (hwe y)
      have h1 : c0 ≤ wT T (δ * psi A L s y) * Real.exp (-psi A L s y) := by
        nlinarith [hexψ y]
      nlinarith
    have : (2 / c0) * (A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)))
        = 2 * (A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)) / c0) := by
      ring
    rw [this]
    linarith
  have hFint : ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E) F y) ∂A.mu < ⊤ := by
    calc ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E) F y) ∂A.mu
        ≤ ∫⁻ y in nz A τ, (ENNReal.ofReal (2 * A.nsq (A.kap + E) h y) + ENNReal.ofReal ((2 / c0) *
            (A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))))) ∂A.mu :=
          lintegral_mono (fun y => (ENNReal.ofReal_le_ofReal (hpt y)).trans ENNReal.ofReal_add_le)
      _ = ∫⁻ y in nz A τ, ENNReal.ofReal (2 * A.nsq (A.kap + E) h y) ∂A.mu +
          ∫⁻ y in nz A τ, ENNReal.ofReal ((2 / c0) *
            (A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)))) ∂A.mu :=
          lintegral_add_left (ENNReal.measurable_ofReal.comp (measurable_const.mul hmeas.1)) _
      _ < ⊤ := by
        apply ENNReal.add_lt_top.2
        constructor
        · have e : ∀ y, ENNReal.ofReal (2 * A.nsq (A.kap + E) h y) =
              ENNReal.ofReal 2 * ENNReal.ofReal (A.nsq (A.kap + E) h y) :=
            fun y => ENNReal.ofReal_mul (by norm_num)
          simp_rw [e]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hhint)
        · have e : ∀ y, ENNReal.ofReal ((2 / c0) *
              (A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)))) =
              ENNReal.ofReal (2 / c0) * ENNReal.ofReal
              (A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) :=
            fun y => ENNReal.ofReal_mul (by positivity)
          simp_rw [e]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
  obtain ⟨G, hG, hGF⟩ := GlobalTheory.T.exists_isSec_extension_of_dense_nz_of_l2 n Y ι La A Λ (A.kap + E) τ F hτ hdense hF hFint
  refine ⟨G, hG, hGF, ?_⟩
  intro P hP

  have hP' : ∀ k, s k (A.pick P) P = 0 := hP
  have hsqP : A.sqn L s P = 0 := by
    simp [WeightedAtlas.sqn, WeightedAtlas.nsq, hP']
  set i := A.pick P with hidef
  set e := A.chart i with hedef
  have hPs : P ∈ e.source := A.mem_pick P
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  set ε : ℝ := Real.exp ((-T - 1) / (δ * n)) with hεdef
  set N : Set Y := (e.source ∩ A.ph E i ⁻¹' Set.Iio (A.ph E i P + 1)) ∩ Ω ∩
    (A.zeroSet s \ {P})ᶜ ∩ {y | A.sqn L s y < ε} with hNdef
  have hNo : IsOpen N := by
    refine ((((A.continuousOn_ph E i).isOpen_inter_preimage e.open_source isOpen_Iio).inter
      hΩo).inter ((hS.subset Set.diff_subset).isClosed.isOpen_compl)).inter
      (isOpen_lt (A.continuous_sqn hs) continuous_const)
  have hPN : P ∈ N := by
    refine ⟨⟨⟨⟨hPs, ?_⟩, hSΩ hP⟩, fun h' => h'.2 rfl⟩, ?_⟩
    · show A.ph E i P < A.ph E i P + 1; linarith
    · show A.sqn L s P < ε; rw [hsqP]; exact Real.exp_pos _
  set O : Set (V n) := e.target ∩ e.symm ⁻¹' N with hOdef
  have hOo : IsOpen O := e.continuousOn_symm.isOpen_inter_preimage e.open_target hNo
  have hpO : e P ∈ O := ⟨e.map_source hPs, by
    show e.symm (e P) ∈ N; rw [e.left_inv hPs]; exact hPN⟩
  set Z : V n → V n := A.zLoc (fun _ _ => 1) s i with hZdef
  set lam : V n → ℝ := fun v => A.ph L i (e.symm v) with hlamdef
  have hdiff : ∀ k, DifferentiableOn ℂ (s k i ∘ e.symm) e.target := fun k => by
    simpa using (hs k).1 i
  have hZd : DifferentiableOn ℂ Z O := by
    intro v hv
    apply DifferentiableAt.differentiableWithinAt
    rw [differentiableAt_euclidean]
    intro k
    simp only [Z, WeightedAtlas.zLoc, PiLp.toLp_apply, div_one]
    exact (hdiff k v hv.1).differentiableAt (e.open_target.mem_nhds hv.1)
  have hZp : Z (e P) = 0 := by
    have h0 : ∀ k, s k i (e.symm (e P)) = 0 := fun k => by rw [e.left_inv hPs]; exact hP' k
    ext k
    simp only [Z, WeightedAtlas.zLoc, PiLp.toLp_apply, div_one]
    first | exact h0 k | simpa using h0 k | (simp; exact h0 k)
  have hdet : (fderiv ℂ Z (e P)).det ≠ 0 := hjac P hP
  have hlam : ContinuousOn lam O :=
    ((A.smooth_ph L i).continuousOn).mono (fun v hv => hv.1)
  set u : V n → ℂ := fun v => h i (e.symm v) - G i (e.symm v) with hudef
  have hu : ContinuousOn u O := by
    have h1 : ContinuousOn (h i ∘ e.symm) O :=
      (hhsec.1 i).continuousOn.mono (fun v hv => ⟨hv.1, hv.2.1.1.2⟩)
    have h2 : ContinuousOn (G i ∘ e.symm) O :=
      (hG.1 i).continuousOn.mono (fun v hv => ⟨hv.1, trivial⟩)
    exact h1.sub h2
  have hZn : ∀ v ∈ e.target, ‖Z v‖ ^ 2 * Real.exp (-lam v) = A.sqn L s (e.symm v) := by
    intro v hv
    have hy : e.symm v ∈ e.source := e.map_target hv
    rw [A.sqn_s_eq (w0 := fun _ _ => 1) hs hy one_ne_zero, e.right_inv hv]
    simp [Z, lam]
    ring
  have hfin : ∫⁻ v in O, ENNReal.ofReal (‖u v‖ ^ 2 *
      Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) < ⊤ := by
    have hNmem : ∀ y ∈ N, y ∈ e.source ∧ A.ph E i y < A.ph E i P + 1 ∧ y ∈ Ω ∧
        y ∉ A.zeroSet s \ {P} ∧ A.sqn L s y < ε :=
      fun y hy => ⟨hy.1.1.1.1, hy.1.1.1.2, hy.1.1.2, hy.1.2, hy.2⟩
    have hUt : IsOpen (e.target ∩ e.symm ⁻¹' nz A τ) :=
      e.continuousOn_symm.isOpen_inter_preimage e.open_target hUo
    set W : Set (V n) := (O ∩ (e.target ∩ e.symm ⁻¹' nz A τ)) \ {e P} with hWdef
    have hWm : MeasurableSet W := (hOo.inter hUt).measurableSet.diff (measurableSet_singleton _)
    have hWO : W ⊆ O := fun v hv => hv.1.1
    have hWt : W ⊆ e.target := fun v hv => hv.1.1.1
    have hnull : volume (e.target ∩ e.symm ⁻¹' (nz A τ)ᶜ) = 0 := by
      have hmu0 : A.mu (e.source ∩ (nz A τ)ᶜ) = 0 :=
        measure_mono_null Set.inter_subset_right (GlobalTheory.T.measure_compl_nonvanishingSet_eq_zero_of_dense n Y ι La A Λ τ hτ hdense)
      rw [A.mu_chart i _ (e.open_source.measurableSet.inter hUo.measurableSet.compl)
        Set.inter_subset_left, e.image_source_inter_eq'] at hmu0
      have hBm : MeasurableSet (e.target ∩ e.symm ⁻¹' (nz A τ)ᶜ) := by
        have : e.target ∩ e.symm ⁻¹' (nz A τ)ᶜ = e.target \ (e.target ∩ e.symm ⁻¹' nz A τ) := by
          ext v; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_diff]
          tauto
        rw [this]; exact e.open_target.measurableSet.diff hUt.measurableSet
      have hco : ContinuousOn (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i (e.symm v))))
          e.target :=
        ENNReal.continuous_ofReal.comp_continuousOn ((A.smooth_ph A.kap i).continuousOn.rexp)
      have hae := (hco.mono Set.inter_subset_left).aemeasurable (μ := volume) hBm
      rw [lintegral_eq_zero_iff' hae] at hmu0
      have h2 : ∀ᵐ v ∂volume, v ∉ e.target ∩ e.symm ⁻¹' (nz A τ)ᶜ := by
        filter_upwards [(ae_restrict_iff' hBm).1 hmu0] with v hv hvB
        have h3 := hv hvB
        simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h3
        exact absurd h3 (not_le.2 (Real.exp_pos _))
      first | exact measure_zero_iff_ae_nmem.2 h2 | exact measure_eq_zero_iff_ae_notMem.2 h2
    have hOW : volume (O \ W) = 0 := by
      apply measure_mono_null (t := {e P} ∪ (e.target ∩ e.symm ⁻¹' (nz A τ)ᶜ))
      · intro v hv
        by_cases hvp : v = e P
        · left; exact hvp
        · right; exact ⟨hv.1.1, fun hU => hv.2 ⟨⟨hv.1, hv.1.1, hU⟩, hvp⟩⟩
      · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
        exact measure_union_null (measure_singleton _) hnull
    have hOWeq : volume.restrict O = volume.restrict W :=
      Measure.restrict_congr_set (ae_eq_set.2 ⟨hOW, by rw [Set.diff_eq_empty.2 hWO]; exact measure_empty⟩)
    rw [hOWeq]
    set c : Y → ℝ := fun y => Real.sqrt (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)) with hcdef
    set D : ι → Y → ℂ := fun j y => (c y : ℂ) * X j y with hDdef
    have hq0 : ∀ y, 0 ≤ wT T (δ * psi A L s y) * Real.exp (-psi A L s y) := fun y =>
      le_trans (mul_nonneg hc0.le (Real.exp_pos _).le) (hwe y)
    have hDsq : ∀ j y, ‖D j y‖ ^ 2 = (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)) * ‖X j y‖ ^ 2 := by
      intro j y
      simp only [D, c, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (hq0 y)]
    have hnsqD : ∀ y, A.nsq (A.kap + E) D y =
        A.nsq (A.kap + E) X y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)) := by
      intro y
      simp only [WeightedAtlas.nsq]
      rw [hDsq]
      ring
    have hcoc : ∀ y ∈ e.source, e y ∈ W → D (A.pick y) y = A.g (A.kap + E) (A.pick y) i y * D i y := by
      intro y hy hyW
      have hyy : e.symm (e y) = y := e.left_inv hy
      have hyU : y ∈ nz A τ := by
        have := hyW.1.2.2; rwa [Set.mem_preimage, hyy] at this
      have hyΩ : y ∈ Ω := by
        have := (hNmem _ hyW.1.1.2).2.2.1; rwa [hyy] at this
      simp only [D, X]
      rw [hhsec.2 (A.pick y) i y hyΩ (A.mem_pick y) hy, hF.2 (A.pick y) i y hyU (A.mem_pick y) hy]
      ring
    have hsymm : AEMeasurable e.symm (volume.restrict W) :=
      (e.continuousOn_symm.mono hWt).aemeasurable hWm
    have hwTc : Continuous (wT T) := by
      unfold wT
      exact continuous_const.div (by fun_prop) (fun x => by positivity)
    have hcm : Measurable c := by
      have : Measurable (fun x : ℝ => Real.sqrt (wT T (δ * x) * Real.exp (-x))) :=
        (Real.continuous_sqrt.comp ((hwTc.comp (continuous_const.mul continuous_id)).mul
          (Real.continuous_exp.comp continuous_neg))).measurable
      exact this.comp hψm
    have hDm : AEMeasurable (D i ∘ e.symm) (volume.restrict W) := by
      have h1 : AEMeasurable (fun v => (c (e.symm v) : ℂ)) (volume.restrict W) :=
        (Complex.measurable_ofReal.comp hcm).comp_aemeasurable hsymm
      have h2 : AEMeasurable (fun v => (θ (δ * psi A L s (e.symm v)) : ℂ)) (volume.restrict W) :=
        (Complex.measurable_ofReal.comp (hθ.1.continuous.measurable.comp
          (measurable_const.mul hψm))).comp_aemeasurable hsymm
      have h3 : AEMeasurable (h i ∘ e.symm) (volume.restrict W) :=
        ((hhsec.1 i).continuousOn.mono (fun v hv => ⟨hWt hv, (hNmem _ (hWO hv).2).2.2.1⟩)).aemeasurable hWm
      have h4 : AEMeasurable (F i ∘ e.symm) (volume.restrict W) :=
        ((hF.1 i).continuousOn.mono (fun v hv => ⟨hWt hv, hv.1.2.2⟩)).aemeasurable hWm
      exact h1.mul ((h2.mul h3).sub h4)
    have hconv := GlobalTheory.T.lintegral_nsq_canonical_add_chart_part n Y ι La A E i W D hWm hWt hcoc hDm
    have hbound : ∫⁻ v in W, ENNReal.ofReal (‖D i (e.symm v)‖ ^ 2 * Real.exp (-A.ph E i (e.symm v))) < ⊤ := by
      rw [← hconv]
      refine lt_of_le_of_lt (lintegral_mono_set ?_)
        (?_ : ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E) D y) ∂A.mu < ⊤)
      · intro y hy
        have := hy.2.1.2.2
        rwa [Set.mem_preimage, e.left_inv hy.1] at this
      · simp_rw [hnsqD]; exact hint
    set K : ℝ := Real.exp (A.ph E i P + 1) / c0 with hKdef
    have hK : 0 ≤ K := by positivity
    calc ∫⁻ v in W, ENNReal.ofReal (‖u v‖ ^ 2 *
          Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v)))))
        ≤ ∫⁻ v in W, ENNReal.ofReal K *
          ENNReal.ofReal (‖D i (e.symm v)‖ ^ 2 * Real.exp (-A.ph E i (e.symm v))) := by
          refine setLIntegral_mono' hWm (fun v hv => ?_)
          rw [← ENNReal.ofReal_mul hK]
          apply ENNReal.ofReal_le_ofReal
          obtain ⟨⟨⟨hvt, hvN⟩, ⟨-, hvU⟩⟩, hvp⟩ := hv
          obtain ⟨hys, hyph, hyΩ, hyS, hysq⟩ := hNmem _ hvN
          have hvy : e (e.symm v) = v := e.right_inv hvt
          have hyZ : e.symm v ∉ A.zeroSet s := by
            intro hz
            apply hvp
            have : e.symm v = P := by
              by_contra hne
              exact hyS ⟨hz, hne⟩
            show v = e P
            rw [← hvy, this]
          have hpos : 0 < A.sqn L s (e.symm v) :=
            bsA_sqn_pos A (by by_contra hc; push_neg at hc; exact hyZ hc)
          have hψlt : δ * psi A L s (e.symm v) ≤ -T - 1 := by
            have hlog : Real.log (A.sqn L s (e.symm v)) < (-T - 1) / (δ * n) :=
              (Real.log_lt_iff_lt_exp hpos).2 hysq
            have hdn : 0 < δ * n := mul_pos hδ hnpos
            have h5 := mul_lt_mul_of_pos_left hlog hdn
            have e2 : (δ * n) * ((-T - 1) / (δ * n)) = -T - 1 := by field_simp
            unfold psi
            calc δ * ((n : ℝ) * Real.log (A.sqn L s (e.symm v)))
                = (δ * n) * Real.log (A.sqn L s (e.symm v)) := by ring
              _ ≤ -T - 1 := by linarith
          have hθ1 : θ (δ * psi A L s (e.symm v)) = 1 := hθ.2.1 _ hψlt
          have hGy : G i (e.symm v) = F i (e.symm v) := hGF i _ hvU hys
          have huX : u v = X i (e.symm v) := by
            simp only [u, X, hθ1, hGy, Complex.ofReal_one, one_mul]
          rw [hZn v hvt, huX, hDsq]
          have hψdef : (n : ℝ) * Real.log (A.sqn L s (e.symm v)) = psi A L s (e.symm v) := rfl
          rw [hψdef]
          have h1 := hwe (e.symm v)
          have h2 : 1 ≤ Real.exp (A.ph E i P + 1) * Real.exp (-A.ph E i (e.symm v)) := by
            rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
          have hx2 : 0 ≤ ‖X i (e.symm v)‖ ^ 2 := by positivity
          have hq := hq0 (e.symm v)
          rw [hKdef, div_mul_eq_mul_div, le_div_iff₀ hc0]
          nlinarith [mul_le_mul_of_nonneg_left h1 hx2,
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hx2 hq)]
      _ = ENNReal.ofReal K * ∫⁻ v in W,
          ENNReal.ofReal (‖D i (e.symm v)‖ ^ 2 * Real.exp (-A.ph E i (e.symm v))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbound
  have key := GlobalTheory.T.eq_zero_at_simple_zero_of_weighted_sq_integrable n hn (e P) O Z lam hOo hpO hZd hZp hdet hlam u hu hfin
  simp only [u, e.left_inv hPs, sub_eq_zero] at key
  exact key.symm
