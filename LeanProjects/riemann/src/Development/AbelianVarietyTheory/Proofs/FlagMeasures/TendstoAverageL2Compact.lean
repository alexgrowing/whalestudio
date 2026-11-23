import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarCompactLtTop
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularBesselModelUnitaryGroup
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal Topology

noncomputable section

namespace GlobalTheory.SgInf.Mollify
variable {k r : ℕ}

theorem continuous_mulPair : Continuous (fun p : Mt k r × Mt k r => rmulM (Matrix.of p.2) p.1) := by
  have h1 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)) := continuous_fst
  have h2 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)) := continuous_snd
  exact h1.matrix_mul h2

theorem nbd_subset_zero (j : ℕ) : nbd k r j ⊆ nbd k r 0 := by
  apply Metric.closedBall_subset_closedBall
  have : (1:ℝ) ≤ (j:ℝ) + 1 := by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  simpa using (div_le_one (by positivity)).2 this

theorem sq_rpow_half (a : ℝ≥0∞) : (a ^ (1/2 : ℝ)) ^ 2 = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

theorem enorm_avg_sq_le {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℝ Wp]
    (μ : Measure (Mt k r)) (S : Set (Mt k r)) (h0 : μ S ≠ 0) (htop : μ S ≠ ⊤) (f : Mt k r → Wp) :
    ‖(μ S).toReal⁻¹ • ∫ y in S, f y ∂μ‖ₑ ^ 2 ≤ (μ S)⁻¹ * ∫⁻ y in S, ‖f y‖ₑ ^ 2 ∂μ := by
  by_cases hf : AEStronglyMeasurable f (μ.restrict S)
  · have hA : ‖∫ y in S, f y ∂μ‖ₑ ≤ ∫⁻ y in S, ‖f y‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    have hC := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (μ := μ.restrict S)
      (by norm_num) hf
    rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero
      ENNReal.ofNat_ne_top, Measure.restrict_apply_univ] at hC
    norm_num at hC
    have hsmul : ‖(μ S).toReal⁻¹ • ∫ y in S, f y ∂μ‖ₑ = (μ S)⁻¹ * ‖∫ y in S, f y ∂μ‖ₑ := by
      rw [enorm_smul, Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_inv_of_pos
        (ENNReal.toReal_pos h0 htop), ENNReal.ofReal_toReal htop]
    rw [hsmul, mul_pow]
    calc (μ S)⁻¹ ^ 2 * ‖∫ y in S, f y ∂μ‖ₑ ^ 2
        ≤ (μ S)⁻¹ ^ 2 * ((∫⁻ y in S, ‖f y‖ₑ ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ) * μ S ^ (1/2 : ℝ)) ^ 2 := by
          gcongr
          exact hA.trans (by simpa using hC)
      _ = (μ S)⁻¹ * ∫⁻ y in S, ‖f y‖ₑ ^ 2 ∂μ := by
          rw [mul_pow, sq_rpow_half, sq_rpow_half]
          simp_rw [ENNReal.rpow_two]
          rw [sq, mul_comm (∫⁻ y in S, ‖f y‖ₑ ^ 2 ∂μ), ← mul_assoc, mul_assoc _ (μ S)⁻¹,
            ENNReal.inv_mul_cancel h0 htop, mul_one]
  · rw [integral_non_aestronglyMeasurable hf]; simp

theorem lint_avg_le {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℝ Wp] (μ : Measure (Mt k r))
    (hμ : IsHaarOn (GG k r) μ) {K K' : Set (Mt k r)} (hK : MeasurableSet K) (hK' : MeasurableSet K')
    (hsub : ∀ y ∈ nbd k r 0, ∀ x ∈ K, rmulM (Matrix.of x) y ∈ K') (h : Mt k r → Wp)
    (hh : StronglyMeasurable h) (j : ℕ) :
    ∫⁻ x in K, ‖avgR μ j h x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x in K', ‖h x‖ₑ ^ 2 ∂μ := by
  haveI : SigmaFinite μ := hμ.1
  set B := nbd k r j with hBdef
  have h0 : μ B ≠ 0 := (nbd_pos hμ j).ne'
  have htop : μ B ≠ ⊤ := (haar_compact_lt_top hμ (isCompact_nbd j)).ne
  set F : Mt k r → ℝ≥0∞ := fun z => ‖h z‖ₑ ^ 2 with hFdef
  have hF : Measurable F := hh.enorm.pow_const 2
  have hG : ∀ᵐ y ∂(μ.restrict B), Matrix.of y ∈ GG k r :=
    ae_restrict_of_ae (ae_iff.2 hμ.2.2.1)
  calc ∫⁻ x in K, ‖avgR μ j h x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in K, (μ B)⁻¹ * ∫⁻ y in B, F (rmulM (Matrix.of x) y) ∂μ ∂μ :=
        lintegral_mono fun x => enorm_avg_sq_le μ B h0 htop (fun y => h (rmulM (Matrix.of x) y))
    _ = (μ B)⁻¹ * ∫⁻ y in B, ∫⁻ x in K, F (rmulM (Matrix.of x) y) ∂μ ∂μ := by
        rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 h0)]
        congr 1
        exact lintegral_lintegral_swap
          ((hF.comp (continuous_mulPair.comp continuous_swap).measurable).aemeasurable)
    _ ≤ (μ B)⁻¹ * ∫⁻ y in B, ∫⁻ x in K', F x ∂μ ∂μ := by
        gcongr _ * ?_
        apply lintegral_mono_ae
        filter_upwards [hG, ae_restrict_mem (isCompact_nbd (k := k) (r := r) j).measurableSet]
          with y hy hyB
        have hl : Continuous (lmulM (Matrix.of y : Mat k r) : Mt k r → Mt k r) :=
          continuous_mulPair.comp (continuous_const.prodMk continuous_id)
        calc ∫⁻ x in K, F (rmulM (Matrix.of x) y) ∂μ
            ≤ ∫⁻ x in K, K'.indicator F (lmulM (Matrix.of y) x) ∂μ := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem hK] with x hx
              · have hm : lmulM (Matrix.of y) x ∈ K' := hsub y (nbd_subset_zero j hyB) x hx
                rw [Set.indicator_of_mem hm]; rfl
          _ ≤ ∫⁻ x, K'.indicator F (lmulM (Matrix.of y) x) ∂μ := setLIntegral_le_lintegral _ _
          _ = ∫⁻ z, K'.indicator F z ∂(μ.map (lmulM (Matrix.of y))) :=
              (lintegral_map (hF.indicator hK') hl.measurable).symm
          _ = ∫⁻ x in K', F x ∂μ := by rw [hμ.2.2.2 _ hy, lintegral_indicator hK']
    _ = ∫⁻ x in K', F x ∂μ := by
        rw [setLIntegral_const, mul_comm _ (μ B), ← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]

theorem of_oneM : (Matrix.of (oneM k r) : Mat k r) = 1 := by ext i j; rfl

theorem rmulM_oneM (x : Mt k r) : rmulM (Matrix.of x) (oneM k r) = x := by
  show (Matrix.of (oneM k r) : Mat k r) * Matrix.of x = x
  rw [of_oneM, Matrix.one_mul]; rfl

theorem tendsto_zero_of_eventually_le {u : ℕ → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in Filter.atTop, u j ≤ M * ENNReal.ofReal ε) :
    Filter.Tendsto u Filter.atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have hT : Filter.Tendsto (fun ε : ℝ => M * ENNReal.ofReal ε) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal ε) (𝓝[>] 0) (𝓝 0) := by
      have := (ENNReal.tendsto_ofReal ((Filter.tendsto_id (x := 𝓝 (0:ℝ))).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))))
      simpa using this
    have := ENNReal.Tendsto.const_mul h1 (Or.inr hM)
    simpa using this
  obtain ⟨ε, hεe, hε0⟩ := ((hT.eventually (gt_mem_nhds he)).and self_mem_nhdsWithin).exists
  filter_upwards [h ε hε0] with j hj
  exact hj.trans hεe.le

theorem tendsto_avg_cont {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℝ Wp] [CompleteSpace Wp] (μ : Measure (Mt k r))
    (hμ : IsHaarOn (GG k r) μ) {K : Set (Mt k r)} (hK : IsCompact K) (c : Mt k r → Wp)
    (hc : Continuous c) :
    Filter.Tendsto (fun j => eLpNorm (fun x => avgR μ j c x - c x) 2 (μ.restrict K)) Filter.atTop
      (𝓝 0) := by
  have hKfin : μ K < ⊤ := haar_compact_lt_top hμ hK
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun C hC => haar_compact_lt_top hμ hC⟩
  apply tendsto_zero_of_eventually_le (M := μ K ^ (2:ℝ≥0∞).toReal⁻¹)
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hKfin.ne)
  intro ε hε
  have hf : Continuous (fun p : Mt k r × Mt k r => c (rmulM (Matrix.of p.2) p.1)) :=
    hc.comp continuous_mulPair
  have huc := ((isCompact_nbd (k := k) (r := r) 0).prod hK).uniformContinuousOn_of_continuous
    hf.continuousOn
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  filter_upwards [Filter.eventually_ge_atTop N] with j hj
  set B := nbd k r j
  have h0 : μ B ≠ 0 := (nbd_pos hμ j).ne'
  have htop : μ B ≠ ⊤ := (haar_compact_lt_top hμ (isCompact_nbd j)).ne
  have hpt : ∀ x ∈ K, ‖avgR μ j c x - c x‖ ≤ ε := by
    intro x hx
    have hint : IntegrableOn (fun y => c (rmulM (Matrix.of x) y)) B μ :=
      ((hf.comp (continuous_id.prodMk continuous_const)).continuousOn).integrableOn_compact
        (isCompact_nbd j) (μ := μ)
    have heq : avgR μ j c x - c x = (μ B).toReal⁻¹ • ∫ y in B, (c (rmulM (Matrix.of x) y) - c x) ∂μ := by
      rw [integral_sub hint (integrableOn_const (hs := htop)), setIntegral_const, smul_sub, smul_smul, measureReal_def,
        inv_mul_cancel₀ (ENNReal.toReal_pos h0 htop).ne', one_smul]
      rfl
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb : ‖∫ y in B, (c (rmulM (Matrix.of x) y) - c x) ∂μ‖ ≤ ε * (μ B).toReal := by
      apply norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 htop)
      intro y hy
      rw [← dist_eq_norm]
      have hy0 : y ∈ nbd k r 0 := nbd_subset_zero j hy
      have h1 := hδε (y, x) ⟨hy0, hx⟩ (oneM k r, x) ⟨oneM_mem_nbd 0, hx⟩ (by
        rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
        calc dist y (oneM k r) ≤ 1 / ((j:ℝ) + 1) := hy
          _ ≤ 1 / ((N:ℝ) + 1) := by gcongr
          _ < δ := hN)
      simp only [rmulM_oneM] at h1
      exact h1.le
    calc (μ B).toReal⁻¹ * ‖∫ y in B, (c (rmulM (Matrix.of x) y) - c x) ∂μ‖
        ≤ (μ B).toReal⁻¹ * (ε * (μ B).toReal) := by gcongr
      _ = ε := by field_simp [(ENNReal.toReal_pos h0 htop).ne']
  have := eLpNorm_le_of_ae_bound (p := 2) (μ := μ.restrict K) (C := ε)
    (f := fun x => avgR μ j c x - c x)
    ((ae_restrict_iff' hK.measurableSet).2 (Filter.Eventually.of_forall hpt))
  simpa [Measure.restrict_apply_univ] using this

theorem eLp2_eq {Wp : Type*} [NormedAddCommGroup Wp] (ν : Measure (Mt k r)) (f : Mt k r → Wp) :
    eLpNorm f 2 ν = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν) ^ (1/2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

theorem stronglyMeasurable_avgR {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℝ Wp]
    (μ : Measure (Mt k r)) [SFinite μ] (j : ℕ) {h : Mt k r → Wp} (hh : StronglyMeasurable h) :
    StronglyMeasurable (avgR μ j h) := by
  have h2 : StronglyMeasurable (fun p : Mt k r × Mt k r => h (rmulM (Matrix.of p.1) p.2)) :=
    hh.comp_measurable (continuous_mulPair.comp continuous_swap).measurable
  exact (h2.integral_prod_right' (ν := μ.restrict (nbd k r j))).const_smul _

theorem map_restrict_le (μ : Measure (Mt k r)) (hU : IsUnimod (GG k r) μ) {x : Mt k r}
    (hx : Matrix.of x ∈ GG k r) {S K' : Set (Mt k r)} (hK' : MeasurableSet K')
    (hS : ∀ y ∈ S, rmulM (Matrix.of x) y ∈ K') :
    (μ.restrict S).map (rmulM (Matrix.of x)) ≤ μ.restrict K' := by
  have hf : Measurable (rmulM (k := k) (r := r) (Matrix.of x)) := (continuous_rmulM _).measurable
  calc (μ.restrict S).map (rmulM (Matrix.of x))
      ≤ (μ.restrict (rmulM (Matrix.of x) ⁻¹' K')).map (rmulM (Matrix.of x)) :=
        Measure.map_mono (Measure.restrict_mono (fun y hy => hS y hy) le_rfl) hf
    _ = μ.restrict K' := by rw [← Measure.restrict_map hf hK', hU.1 _ hx]

end GlobalTheory.SgInf.Mollify

open GlobalTheory.SgInf.Mollify in

theorem GlobalTheory.SgInf.tendsto_average_L2 : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → ∀ {Wp : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (g : Mt k r → Wp),
    (∀ K : Set (Mt k r), IsCompact K → AEStronglyMeasurable g (μ.restrict K) ∧
      ∫⁻ x in K, (‖g x‖₊ : ENNReal) ^ 2 ∂μ < ⊤) →
    ∀ K : Set (Mt k r), IsCompact K → Filter.Tendsto (fun j : ℕ =>
      ∫⁻ x in K, (‖avgR μ j g x - g x‖₊ : ENNReal) ^ 2 ∂μ) Filter.atTop (nhds 0) := by
  intro k r μ hμ Wp _ _ _ g hg K hK
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  haveI : SigmaFinite μ := hμ.1
  have hU := GlobalTheory.SgInf.isUnimod_GG k r μ hμ
  set K' := (fun p : Mt k r × Mt k r => rmulM (Matrix.of p.2) p.1) '' (nbd k r 0 ×ˢ K) with hK'def
  have hK'c : IsCompact K' := ((isCompact_nbd 0).prod hK).image continuous_mulPair
  have hK'm : MeasurableSet K' := hK'c.measurableSet
  have hsub : ∀ y ∈ nbd k r 0, ∀ x ∈ K, rmulM (Matrix.of x) y ∈ K' :=
    fun y hy x hx => ⟨(y, x), ⟨hy, hx⟩, rfl⟩
  have hKK' : K ⊆ K' := fun x hx => by simpa [rmulM_oneM] using hsub _ (oneM_mem_nbd 0) x hx
  have hle : μ.restrict K ≤ μ.restrict K' := Measure.restrict_mono hKK' le_rfl
  obtain ⟨hgm, hgI⟩ := hg K' hK'c
  set ν := μ.restrict K' with hνdef
  haveI : IsFiniteMeasure ν := ⟨by rw [Measure.restrict_apply_univ]; exact haar_compact_lt_top hμ hK'c⟩
  set g' := hgm.mk g
  have hg'm : StronglyMeasurable g' := hgm.stronglyMeasurable_mk
  have hgg' : g =ᵐ[ν] g' := hgm.ae_eq_mk
  have hmemg : MemLp g 2 ν := by
    refine ⟨hgm, ?_⟩
    rw [eLp2_eq]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hgI.ne
  have hmem : MemLp g' 2 ν := hmemg.ae_eq hgg'

  suffices H : Filter.Tendsto (fun j : ℕ => eLpNorm (fun x => avgR μ j g x - g x) 2 (μ.restrict K))
      Filter.atTop (nhds 0) by
    have := ENNReal.Tendsto.pow (n := 2) H
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
    refine this.congr fun j => ?_
    rw [eLp2_eq, sq_rpow_half]; rfl
  apply tendsto_zero_of_eventually_le (M := 3) (by norm_num)
  intro ε hε
  set δ := ENNReal.ofReal ε
  have hδ0 : δ ≠ 0 := by simpa [δ] using hε
  obtain ⟨c, hcδ, hcmem⟩ := hmem.exists_boundedContinuous_eLpNorm_sub_le ENNReal.ofNat_ne_top hδ0
  set h : Mt k r → Wp := g' - (c : Mt k r → Wp) with hhdef
  have hhm : StronglyMeasurable h := hg'm.sub c.continuous.stronglyMeasurable

  have hA : ∀ j, eLpNorm (avgR μ j h) 2 (μ.restrict K) ≤ δ := by
    intro j
    refine le_trans ?_ hcδ
    rw [eLp2_eq, eLp2_eq]
    exact ENNReal.rpow_le_rpow (lint_avg_le μ hμ hK.measurableSet hK'm hsub h hhm j) (by norm_num)
  have hC : eLpNorm (fun x => c x - g' x) 2 (μ.restrict K) ≤ δ := by
    refine le_trans (eLpNorm_mono_measure _ hle) ?_
    rw [show (fun x => c x - g' x) = (c : Mt k r → Wp) - g' from rfl, eLpNorm_sub_comm]; exact hcδ
  have hB := (tendsto_avg_cont μ hμ hK c c.continuous).eventually
    (Iic_mem_nhds (show (0:ℝ≥0∞) < δ from pos_iff_ne_zero.2 hδ0))
  filter_upwards [hB] with j hj

  have hid : (fun x => avgR μ j g x - g x) =ᵐ[μ.restrict K]
      (fun x => (avgR μ j h x + (avgR μ j c x - c x)) + (c x - g' x)) := by
    filter_upwards [ae_restrict_of_ae (ae_iff.2 hμ.2.2.1), ae_restrict_mem hK.measurableSet,
      (Measure.absolutelyContinuous_of_le hle).ae_le hgg'] with x hxG hxK hxg
    have hmap := map_restrict_le μ hU hxG (S := nbd k r j) hK'm
      (fun y hy => hsub y (nbd_subset_zero j hy) x hxK)
    have hf : Measurable (rmulM (k := k) (r := r) (Matrix.of x)) := (continuous_rmulM _).measurable
    have hae : ∀ᵐ y ∂(μ.restrict (nbd k r j)), g (rmulM (Matrix.of x) y) = g' (rmulM (Matrix.of x) y) :=
      ae_of_ae_map hf.aemeasurable ((Measure.absolutelyContinuous_of_le hmap).ae_le hgg')
    have hi1 : Integrable (fun y => g' (rmulM (Matrix.of x) y)) (μ.restrict (nbd k r j)) :=
      ((hmem.integrable one_le_two).mono_measure hmap).comp_measurable hf
    have hi2 : Integrable (fun y => c (rmulM (Matrix.of x) y)) (μ.restrict (nbd k r j)) :=
      ((hcmem.integrable one_le_two).mono_measure hmap).comp_measurable hf
    have e1 : avgR μ j g x = avgR μ j g' x := by
      unfold avgR; rw [integral_congr_ae hae]
    have e2 : avgR μ j h x = avgR μ j g' x - avgR μ j c x := by
      unfold avgR
      rw [← smul_sub, ← integral_sub hi1 hi2]
      rfl
    rw [e1, e2, hxg]
    abel
  rw [eLpNorm_congr_ae hid]
  have m1 : AEStronglyMeasurable (avgR μ j h) (μ.restrict K) :=
    (stronglyMeasurable_avgR μ j hhm).aestronglyMeasurable
  have m2 : AEStronglyMeasurable (fun x => avgR μ j c x - c x) (μ.restrict K) :=
    ((stronglyMeasurable_avgR μ j c.continuous.stronglyMeasurable).sub
      c.continuous.stronglyMeasurable).aestronglyMeasurable
  have m3 : AEStronglyMeasurable (fun x => c x - g' x) (μ.restrict K) :=
    (c.continuous.stronglyMeasurable.sub hg'm).aestronglyMeasurable
  calc eLpNorm (fun x => (avgR μ j h x + (avgR μ j c x - c x)) + (c x - g' x)) 2 (μ.restrict K)
      ≤ eLpNorm (fun x => avgR μ j h x + (avgR μ j c x - c x)) 2 (μ.restrict K)
        + eLpNorm (fun x => c x - g' x) 2 (μ.restrict K) :=
        eLpNorm_add_le (m1.add m2) m3 one_le_two
    _ ≤ (eLpNorm (avgR μ j h) 2 (μ.restrict K)
        + eLpNorm (fun x => avgR μ j c x - c x) 2 (μ.restrict K))
        + eLpNorm (fun x => c x - g' x) 2 (μ.restrict K) := by
        gcongr
        exact eLpNorm_add_le m1 m2 one_le_two
    _ ≤ (δ + δ) + δ := by gcongr; exact hA j
    _ = 3 * ENNReal.ofReal ε := by ring

example : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → ∀ {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (g : Mt k r → Wp), (∀ K : Set (Mt k r), IsCompact K → AEStronglyMeasurable g (μ.restrict K) ∧ ∫⁻ x in K, (‖g x‖₊ : ENNReal) ^ 2 ∂μ < ⊤) → ∀ K : Set (Mt k r), IsCompact K → Filter.Tendsto (fun j : ℕ => ∫⁻ x in K, (‖avgR μ j g x - g x‖₊ : ENNReal) ^ 2 ∂μ) Filter.atTop (nhds 0) := GlobalTheory.SgInf.tendsto_average_L2
