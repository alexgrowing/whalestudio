import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHolomorphicExtensionNearZerosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothCutoffSlopeThreeQuartersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableNsqExtendAndPsiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedEstimateEtalePartManifoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionAcrossHypersurfaceValuesAtZerosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSublevelTailLeOfFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureComplNonvanishingSetEqZeroOfDenseStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem norm_sub_sq_le_of_split (u v : ℂ) : ‖u - v‖ ^ 2 ≤ 32 / 31 * ‖v‖ ^ 2 + 32 * ‖u‖ ^ 2 := by
  have h1 : ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le u v
  have h0 : 0 ≤ ‖u - v‖ := norm_nonneg _
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  nlinarith [sq_nonneg (‖v‖ - 31 * ‖u‖)]

theorem weight_ge_of_nonpos (δ t : ℝ) (hδ : 0 < δ) (ht : t ≤ 0) :
    min 1 (1 / (2 * δ ^ 2)) ≤ 1 / (1 + (δ * t) ^ 2) * Real.exp (-t) := by
  have hc1 : min 1 (1 / (2 * δ ^ 2)) ≤ 1 := min_le_left _ _
  have hc2 : min 1 (1 / (2 * δ ^ 2)) ≤ 1 / (2 * δ ^ 2) := min_le_right _ _
  have hcd : min 1 (1 / (2 * δ ^ 2)) * δ ^ 2 ≤ 1 / 2 := by
    calc min 1 (1 / (2 * δ ^ 2)) * δ ^ 2 ≤ 1 / (2 * δ ^ 2) * δ ^ 2 :=
          mul_le_mul_of_nonneg_right hc2 (sq_nonneg δ)
      _ = 1 / 2 := by field_simp
  have hexp : 1 + (-t) + (-t) ^ 2 / 2 ≤ Real.exp (-t) := Real.quadratic_le_exp_of_nonneg (by linarith)
  have hpos : 0 < 1 + (δ * t) ^ 2 := by positivity
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_right hcd (sq_nonneg t)]

theorem final_pointwise_le (n : ℕ) (x T tv ep e : ℝ) (Fp hp : ℂ) (hep : 0 ≤ ep) (he : 0 ≤ e) :
    2 ^ n * (1 / (1 + x ^ 2) * (‖Fp‖ ^ 2 * ep) * e) ≤
      2 ^ n * (32 / 31 * ((‖(tv : ℂ) * hp - Fp‖ ^ 2 * ep) * (wT T x * e)) +
        32 * (tv ^ 2 * (1 / (1 + x ^ 2) * (‖hp‖ ^ 2 * ep) * e))) := by
  have hnorm := norm_sub_sq_le_of_split ((tv : ℂ) * hp) ((tv : ℂ) * hp - Fp)
  rw [sub_sub_cancel] at hnorm
  have hu : ‖(tv : ℂ) * hp‖ ^ 2 = tv ^ 2 * ‖hp‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hu] at hnorm
  have hγ0 : 0 ≤ 1 / (1 + x ^ 2) := by positivity
  have hmin : 0 < 1 + min (x ^ 2) ((T + 1) ^ 2) :=
    lt_of_lt_of_le one_pos (le_add_of_nonneg_right (le_min (sq_nonneg _) (sq_nonneg _)))
  have hγw : 1 / (1 + x ^ 2) ≤ wT T x := by
    unfold wT
    exact one_div_le_one_div_of_le hmin (by linarith [min_le_left (x ^ 2) ((T + 1) ^ 2)])
  have hv0 : 0 ≤ ‖(tv : ℂ) * hp - Fp‖ ^ 2 := sq_nonneg _
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n)
  have h1 : 1 / (1 + x ^ 2) * (‖Fp‖ ^ 2 * ep) * e ≤
      1 / (1 + x ^ 2) * e * ep * (32 / 31 * ‖(tv : ℂ) * hp - Fp‖ ^ 2 + 32 * (tv ^ 2 * ‖hp‖ ^ 2)) := by
    calc 1 / (1 + x ^ 2) * (‖Fp‖ ^ 2 * ep) * e = 1 / (1 + x ^ 2) * e * ep * ‖Fp‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (by positivity)
  have h2 : 1 / (1 + x ^ 2) * (32 / 31 * ‖(tv : ℂ) * hp - Fp‖ ^ 2 * ep * e) ≤
      wT T x * (32 / 31 * ‖(tv : ℂ) * hp - Fp‖ ^ 2 * ep * e) :=
    mul_le_mul_of_nonneg_right hγw (by positivity)
  nlinarith [h1, h2]

end GlobalTheory

namespace GlobalTheory

theorem l2_extension_of_etale_coordinates : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ hS : (A.zeroSet s).Finite, (∀ P ∈ A.zeroSet s, jacAt A s P ≠ 0) → (∀ y, A.sqn L s y ≤ 1) → ∀ δ : ℝ, 0 < δ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n) (β : ι → Y → ℂ), (A.IsSec Λ τ ∧ A.Pos Λ (fun _ => 0) ∧ Etale A (nz A τ) z ∧ A.IsFrameOn (A.kap + E) (nz A τ) β ∧ Dense (nz A τ) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y) → ∀ f : Y → ℂ, ∃ F : ι → Y → ℂ, A.IsSec (A.kap + E) F ∧ (∀ P ∈ A.zeroSet s, F (A.pick P) P = f P) ∧ ∫⁻ y, ENNReal.ofReal (2 ^ n * (1 / (1 + (δ * psi A L s y) ^ 2) * A.nsq (A.kap + E) F y * Real.exp (-psi A L s y))) ∂A.mu ≤ ENNReal.ofReal (34 / δ * (resConst n * ∑ P ∈ hS.toFinset, resSq A E L s P (f P))) := by
  intro n Y _ _ _ _ _ _ ι La _ A hn E L s hs hS hjac hsq δ hδ hlevi Λ τ z β hΛ f
  obtain ⟨hτ, hpos, het, hfr, hdense, C, hC, hCb⟩ := hΛ
  have hres_nn : ∀ P, 0 ≤ resSq A E L s P (f P) := fun P => by
    unfold resSq; positivity
  have hSg_nn : 0 ≤ ∑ P ∈ hS.toFinset, resSq A E L s P (f P) :=
    Finset.sum_nonneg fun P _ => hres_nn P
  rcases hSg_nn.eq_or_lt with h0 | hSpos
  · refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩
    · unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn
      exact ⟨fun i => differentiableOn_const 0, fun i j y _ _ _ => by simp⟩
    · intro P hP
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun P _ => hres_nn P)).1 h0.symm P
        (hS.mem_toFinset.2 hP)
      unfold resSq at hz
      have hexp := Real.exp_pos (-A.ph E (A.pick P) P + (n : ℝ) * A.ph L (A.pick P) P)
      have h1 : ‖f P / jacAt A s P‖ ^ 2 = 0 := by
        rcases mul_eq_zero.1 hz with h | h
        · exact h
        · exact absurd h hexp.ne'
      have h2 : f P / jacAt A s P = 0 := by simpa using h1
      rcases div_eq_zero_iff.1 h2 with h | h
      · simp [h]
      · exact absurd h (hjac P hP)
    · simp [WeightedAtlas.nsq]
  · have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    obtain ⟨Ω, h, m, ⟨hΩo, hhsec, hh0⟩, hm, hmΩ, hval, hshell, hfin⟩ :=
      GlobalTheory.T.exists_local_holomorphic_extension_near_zeros n Y ι La A hn E L s hs hS hjac f δ hδ
    obtain ⟨hNm, hψm⟩ := GlobalTheory.T.measurable_nsq_and_psi_of_isSecOn n Y ι La A (A.kap + E) Ω h hΩo hhsec hh0
    have hψm' := hψm L s hs
    have hN_nn : ∀ (la : La) (F : ι → Y → ℂ) y, 0 ≤ A.nsq la F y := fun la F y => by
      unfold WeightedAtlas.nsq; positivity
    have hsqn_nn : ∀ y, 0 ≤ A.sqn L s y := fun y =>
      Finset.sum_nonneg fun k _ => hN_nn L (s k) y
    have hψle : ∀ y, psi A L s y ≤ 0 := fun y => by
      unfold psi
      exact mul_nonpos_of_nonneg_of_nonpos hn0.le (Real.log_nonpos (hsqn_nn y) (hsq y))
    have hc0 : 0 < min 1 (1 / (2 * δ ^ 2)) := lt_min one_pos (by positivity)
    have hL2 : ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu < ⊤ := by
      have hle : ∀ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ≤
          ENNReal.ofReal (1 / min 1 (1 / (2 * δ ^ 2))) * ENNReal.ofReal (1 / (1 + (δ * psi A L s y) ^ 2) *
            A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) := by
        intro y
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hw := weight_ge_of_nonpos δ (psi A L s y) hδ (hψle y)
        have hN := hN_nn (A.kap + E) h y
        have key : min 1 (1 / (2 * δ ^ 2)) * A.nsq (A.kap + E) h y ≤
            1 / (1 + (δ * psi A L s y) ^ 2) * A.nsq (A.kap + E) h y * Real.exp (-psi A L s y) := by
          nlinarith [mul_le_mul_of_nonneg_right hw hN]
        calc A.nsq (A.kap + E) h y
            = 1 / min 1 (1 / (2 * δ ^ 2)) * (min 1 (1 / (2 * δ ^ 2)) * A.nsq (A.kap + E) h y) := by
              field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left key (by positivity)
      calc _ ≤ ∫⁻ y, ENNReal.ofReal (1 / min 1 (1 / (2 * δ ^ 2))) *
            ENNReal.ofReal (1 / (1 + (δ * psi A L s y) ^ 2) * A.nsq (A.kap + E) h y *
              Real.exp (-psi A L s y)) ∂A.mu := lintegral_mono hle
        _ = ENNReal.ofReal (1 / min 1 (1 / (2 * δ ^ 2))) *
            ∫⁻ y, ENNReal.ofReal (1 / (1 + (δ * psi A L s y) ^ 2) * A.nsq (A.kap + E) h y *
              Real.exp (-psi A L s y)) ∂A.mu := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
    set K : ℝ := Real.pi ^ n / ((n - 1).factorial : ℝ) / δ *
        ∑ P ∈ hS.toFinset, resSq A E L s P (f P) with hK
    have hKpos : 0 < K := by
      have := Real.pi_pos
      have : (0:ℝ) < ((n - 1).factorial : ℝ) := by positivity
      exact mul_pos (by positivity) hSpos
    have hggm : Measurable (fun y => ENNReal.ofReal (1 / (1 + (δ * psi A L s y) ^ 2) *
        A.nsq (A.kap + E) h y * Real.exp (-psi A L s y))) := by
      refine Measurable.ennreal_ofReal ?_
      exact ((measurable_const.div (measurable_const.add ((hψm'.const_mul δ).pow_const 2))).mul
        hNm).mul hψm'.neg.exp
    obtain ⟨T0, hT0⟩ := GlobalTheory.T.lintegral_sublevel_tail_le_of_finite Y A.mu
      (fun y => ENNReal.ofReal (1 / (1 + (δ * psi A L s y) ^ 2) *
        A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)))
      (fun y => δ * psi A L s y) (hψm'.const_mul δ) hfin hggm
      (ENNReal.ofReal (K / 8)) (ENNReal.ofReal_pos.2 (by positivity))
    set T : ℝ := max 300 (max T0 (2 - δ * n * Real.log m)) with hT
    have hT300 : 300 ≤ T := le_max_left _ _
    have hTT0 : T0 ≤ T := le_trans (le_max_left _ _) (le_max_right _ _)
    have hT1 : 2 - δ * n * Real.log m ≤ T := le_trans (le_max_right _ _) (le_max_right _ _)
    have hdeep : ∀ y, δ * psi A L s y ≤ -T + 1 → A.sqn L s y < m := by
      intro y hy
      rcases (hsqn_nn y).eq_or_lt with h0 | hp
      · rw [← h0]; exact hm
      · have hdn : 0 < δ * n := mul_pos hδ hn0
        have h1 : δ * n * Real.log (A.sqn L s y) < δ * n * Real.log m := by
          have : δ * psi A L s y = δ * n * Real.log (A.sqn L s y) := by unfold psi; ring
          linarith
        have h2 := lt_of_mul_lt_mul_left h1 hdn.le
        exact (Real.log_lt_log_iff hp hm).1 h2
    have hsubΩ : ∀ y, y ∉ A.zeroSet s → δ * psi A L s y ≤ -T + 1 → y ∈ Ω :=
      fun y _ hy => hmΩ y (hdeep y hy)
    have hzΩ : A.zeroSet s ⊆ Ω := by
      intro y hy
      have hy' : ∀ k, s k (A.pick y) y = 0 := hy
      apply hmΩ
      have : A.sqn L s y = 0 := by
        unfold WeightedAtlas.sqn
        apply Finset.sum_eq_zero
        intro k _
        unfold WeightedAtlas.nsq
        rw [hy' k]; simp
      rw [this]; exact hm
    obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_smoothCutoff_slope_three_quarters T
    obtain ⟨F, hFsec, hFbd⟩ := GlobalTheory.T.twistedEstimate_etalePart_manifold n Y ι La A E L s hs hsq δ hδ hlevi Λ τ z β
      ⟨hτ, hpos, het, hfr, hdense, C, hC, hCb⟩ Ω h T θ ⟨hΩo, hhsec, hh0⟩ hT300 hθ hsubΩ hL2
    have hshellT := hshell T (by linarith)
    have hFbd' : (∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E)
        (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y *
          (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu) ≤ ENNReal.ofReal (62 * K) := by
      calc _ ≤ _ := hFbd
        _ ≤ 30 * ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ *
              ∑ P ∈ hS.toFinset, resSq A E L s P (f P)) := by gcongr
        _ = ENNReal.ofReal (62 * K) := by
          rw [show (30 : ℝ≥0∞) = ENNReal.ofReal 30 by simp, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; rw [hK]; ring
    obtain ⟨G, hGsec, hGF, hGP⟩ := GlobalTheory.T.extension_across_hypersurface_values_at_zeros n Y ι La A hn E L s hs hS hjac hsq δ hδ Λ τ hτ
      hdense Ω h T θ ⟨hΩo, hhsec, hh0⟩ hzΩ hθ hL2 F hFsec (lt_of_le_of_lt hFbd' ENNReal.ofReal_lt_top)
    refine ⟨G, hGsec, fun P hP => (hGP P hP).trans (hval P hP), ?_⟩
    have hnull : A.mu (nz A τ)ᶜ = 0 := GlobalTheory.T.measure_compl_nonvanishingSet_eq_zero_of_dense n Y ι La A Λ τ hτ hdense
    have hnzm : MeasurableSet (nz A τ) := het.isOpen.measurableSet
    have hSm : MeasurableSet {y | δ * psi A L s y ≤ -T + 1} :=
      measurableSet_le (hψm'.const_mul δ) measurable_const
    have hae : ∀ᵐ y ∂A.mu, y ∈ nz A τ := by
      rw [ae_iff]; exact hnull
    have hpt : ∀ᵐ y ∂A.mu, ENNReal.ofReal (2 ^ n * (1 / (1 + (δ * psi A L s y) ^ 2) *
        A.nsq (A.kap + E) G y * Real.exp (-psi A L s y))) ≤
        ENNReal.ofReal (2 ^ n) * (ENNReal.ofReal (32 / 31) * (nz A τ).indicator (fun y =>
          ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y *
            (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)))) y +
          ENNReal.ofReal 32 * {y | δ * psi A L s y ≤ -T + 1}.indicator (fun y =>
            ENNReal.ofReal (1 / (1 + (δ * psi A L s y) ^ 2) *
              A.nsq (A.kap + E) h y * Real.exp (-psi A L s y))) y) := by
      filter_upwards [hae] with y hy
      rw [Set.indicator_of_mem hy]
      have hGy : G (A.pick y) y = F (A.pick y) y := hGF (A.pick y) y hy (A.mem_pick y)
      have hθ01 := hθ.2.2.2.1 (δ * psi A L s y)
      have hind : ENNReal.ofReal (θ (δ * psi A L s y) ^ 2 * (1 / (1 + (δ * psi A L s y) ^ 2) *
          A.nsq (A.kap + E) h y * Real.exp (-psi A L s y))) ≤
          {y | δ * psi A L s y ≤ -T + 1}.indicator (fun y =>
            ENNReal.ofReal (1 / (1 + (δ * psi A L s y) ^ 2) *
              A.nsq (A.kap + E) h y * Real.exp (-psi A L s y))) y := by
        by_cases hyS : δ * psi A L s y ≤ -T + 1
        · rw [Set.indicator_of_mem (show y ∈ {y | δ * psi A L s y ≤ -T + 1} from hyS)]
          apply ENNReal.ofReal_le_ofReal
          have hX : 0 ≤ 1 / (1 + (δ * psi A L s y) ^ 2) * A.nsq (A.kap + E) h y *
              Real.exp (-psi A L s y) := by
            have := hN_nn (A.kap + E) h y
            positivity
          apply mul_le_of_le_one_left hX
          nlinarith [hθ01.1, hθ01.2]
        · have h0 : θ (δ * psi A L s y) = 0 := hθ.2.2.1 _ (le_of_lt (not_le.1 hyS))
          rw [h0]; simp
      have hreal := final_pointwise_le n (δ * psi A L s y) T (θ (δ * psi A L s y))
        (Real.exp (-A.ph (A.kap + E) (A.pick y) y)) (Real.exp (-psi A L s y))
        (F (A.pick y) y) (h (A.pick y) y) (Real.exp_pos _).le (Real.exp_pos _).le
      have hnG : A.nsq (A.kap + E) G y =
          ‖F (A.pick y) y‖ ^ 2 * Real.exp (-A.ph (A.kap + E) (A.pick y) y) := by
        simp only [WeightedAtlas.nsq, hGy]
      have ha0 : 0 ≤ A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y *
          (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)) := by
        have := hN_nn (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y
        have hw : 0 ≤ wT T (δ * psi A L s y) := by unfold wT; positivity
        positivity
      have hb0 : 0 ≤ θ (δ * psi A L s y) ^ 2 * (1 / (1 + (δ * psi A L s y) ^ 2) *
          A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) := by
        have := hN_nn (A.kap + E) h y
        positivity
      calc ENNReal.ofReal (2 ^ n * (1 / (1 + (δ * psi A L s y) ^ 2) *
            A.nsq (A.kap + E) G y * Real.exp (-psi A L s y)))
          ≤ ENNReal.ofReal (2 ^ n * (32 / 31 * (A.nsq (A.kap + E)
              (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y *
              (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) +
              32 * (θ (δ * psi A L s y) ^ 2 * (1 / (1 + (δ * psi A L s y) ^ 2) *
                A.nsq (A.kap + E) h y * Real.exp (-psi A L s y))))) := by
            apply ENNReal.ofReal_le_ofReal
            rw [hnG]
            exact hreal
        _ = ENNReal.ofReal (2 ^ n) * (ENNReal.ofReal (32 / 31) * ENNReal.ofReal (A.nsq (A.kap + E)
              (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y *
              (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) +
              ENNReal.ofReal 32 * ENNReal.ofReal (θ (δ * psi A L s y) ^ 2 *
                (1 / (1 + (δ * psi A L s y) ^ 2) *
                A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)))) := by
            have h2n : (0:ℝ) ≤ 2 ^ n := by positivity
            have h3 : (0:ℝ) ≤ 32 / 31 := by norm_num
            have h4 : (0:ℝ) ≤ 32 := by norm_num
            rw [ENNReal.ofReal_mul h2n, ENNReal.ofReal_add (mul_nonneg h3 ha0) (mul_nonneg h4 hb0),
              ENNReal.ofReal_mul h3, ENNReal.ofReal_mul h4]
        _ ≤ _ := by gcongr
    have hfac : ((n - 1).factorial : ℝ) ≠ 0 := by positivity
    calc _ ≤ ∫⁻ y, ENNReal.ofReal (2 ^ n) * (ENNReal.ofReal (32 / 31) * (nz A τ).indicator (fun y =>
          ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y *
            (wT T (δ * psi A L s y) * Real.exp (-psi A L s y)))) y +
          ENNReal.ofReal 32 * {y | δ * psi A L s y ≤ -T + 1}.indicator (fun y =>
            ENNReal.ofReal (1 / (1 + (δ * psi A L s y) ^ 2) *
              A.nsq (A.kap + E) h y * Real.exp (-psi A L s y))) y) ∂A.mu := lintegral_mono_ae hpt
      _ = ENNReal.ofReal (2 ^ n) * (ENNReal.ofReal (32 / 31) * (∫⁻ y in nz A τ,
          ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y *
            (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu) +
          ENNReal.ofReal 32 * ∫⁻ y in {y | δ * psi A L s y ≤ -T + 1},
            ENNReal.ofReal (1 / (1 + (δ * psi A L s y) ^ 2) *
              A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_right _ ((hggm.indicator hSm).const_mul _),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator hnzm,
            lintegral_indicator hSm]
      _ ≤ ENNReal.ofReal (2 ^ n) * (ENNReal.ofReal (32 / 31) * ENNReal.ofReal (62 * K) +
          ENNReal.ofReal 32 * ENNReal.ofReal (K / 8)) := by
          gcongr
          all_goals first | exact hFbd' | exact hT0 T hTT0
      _ = ENNReal.ofReal (34 / δ * (resConst n * ∑ P ∈ hS.toFinset, resSq A E L s P (f P))) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hK, resConst]
          field_simp
          ring

end GlobalTheory
