import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarGlueSectionByPartitionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNsqCanonicalAddChartPartStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.GlueEnergy

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] {A : WeightedAtlas n Y ι La}

theorem exists_bound (C : Cover A) : ∃ B : ℝ, 0 ≤ B ∧ ∀ a b j, ∀ v ∈ ball (C.c b) (C.r b),
    ‖wdb n j (fun x => (C.chi a ((A.chart (C.idx b)).symm x) : ℂ)) v‖ ≤ B := by
  have h : ∀ p : Fin C.m × Fin C.m × Fin n, ∃ B : ℝ, ∀ v ∈ closedBall (C.c p.2.1) (C.r p.2.1),
      ‖wdb n p.2.2 (fun x => (C.chi p.1 ((A.chart (C.idx p.2.1)).symm x) : ℂ)) v‖ ≤ B := by
    rintro ⟨a, b, j⟩
    apply (isCompact_closedBall _ _).exists_bound_of_continuousOn
    refine ContinuousOn.mono ?_ (C.sub b)
    have h1 : ContDiffOn ℝ ∞ (fun x => (C.chi a ((A.chart (C.idx b)).symm x) : ℂ))
        (A.chart (C.idx b)).target :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (C.smooth a (C.idx b))
    have h2 := h1.continuousOn_fderiv_of_isOpen (A.chart (C.idx b)).open_target (by simp)
    unfold wdb
    exact ((h2.clm_apply continuousOn_const).add
      (continuousOn_const.mul (h2.clm_apply continuousOn_const))).div_const _
  choose B hB using h
  refine ⟨∑ p, |B p|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun a b j v hv => ?_⟩
  exact ((hB (a, b, j) v (ball_subset_closedBall hv)).trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun p => |B p|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _))

theorem wdb_eq_zero (C : Cover A) (a : Fin C.m) (i : ι) (j : Fin n) (v : V n)
    (hv : v ∈ (A.chart i).target)
    (h : (A.chart i).symm v ∉
      (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) :
    wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v = 0 := by
  have h1 : (A.chart i).symm v ∉ tsupport (C.chi a) := fun h' => h (C.supp a h')
  have h2 := notMem_tsupport_iff_eventuallyEq.mp h1
  have h3 := ((A.chart i).continuousAt_symm hv).eventually h2
  have h4 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) =ᶠ[𝓝 v] fun _ => 0 :=
    h3.mono fun x hx => by simp only [Pi.zero_apply] at hx; simp [hx]
  unfold wdb
  rw [h4.fderiv_eq]
  simp

theorem sq_sum_le {m : ℕ} (x d : Fin m → ℂ) (B : ℝ) (e : Fin m → ℝ)
    (h : ∀ a, ‖x a * d a‖ ^ 2 ≤ B ^ 2 * e a) :
    ‖∑ a, x a * d a‖ ^ 2 ≤ m * B ^ 2 * ∑ a, e a := by
  calc ‖∑ a, x a * d a‖ ^ 2 ≤ (∑ a, ‖x a * d a‖) ^ 2 := by
        gcongr; exact norm_sum_le _ _
    _ ≤ m * ∑ a, ‖x a * d a‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => ‖x a * d a‖)
    _ ≤ m * ∑ a, B ^ 2 * e a := by gcongr with a; exact h a
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

theorem energy_glue_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (F0 : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), A.IsSSec (A.kap + la) F0 → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → n1 C la (glue C la u) ≤ ENNReal.ofReal K * ∑ a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
  intro n Y _ _ _ _ _ ι La _ A C
  obtain ⟨B, hB0, hB⟩ := exists_bound C
  refine ⟨C.m * (n * (C.m * B ^ 2)), by positivity, fun la F0 u hF hu => ?_⟩
  set D : Fin C.m → ι → Y → ℂ := fun a i y =>
    A.g (A.kap + la) i (C.idx a) y * u a (A.chart (C.idx a) y) - F0 i y with hD
  set U : Fin C.m → Set Y := fun a =>
    (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) with hU
  have hUo : ∀ a, IsOpen (U a) := fun a => (A.chart (C.idx a)).isOpen_inter_preimage isOpen_ball
  have hbt : ∀ b, ball (C.c b) (C.r b) ⊆ (A.chart (C.idx b)).target := fun b =>
    ball_subset_closedBall.trans (C.sub b)
  set W : Fin C.m → Fin C.m → Set (V n) := fun b a =>
    ball (C.c b) (C.r b) ∩ ((A.chart (C.idx b)).target ∩ (A.chart (C.idx b)).symm ⁻¹' U a) with hW
  have hWo : ∀ b a, IsOpen (W b a) := fun b a =>
    isOpen_ball.inter ((A.chart (C.idx b)).isOpen_inter_preimage_symm (hUo a))
  have hDc : ∀ b a, ContinuousOn (D a (C.idx b) ∘ (A.chart (C.idx b)).symm) (W b a) := by
    intro b a
    have hov : W b a ⊆ ovl A.chart (C.idx b) (C.idx a) := fun v hv => ⟨hv.2.1, hv.2.2.1⟩
    have h1 := (A.holo_g (A.kap + la) (C.idx b) (C.idx a)).continuousOn.mono hov
    have h2 := (A.holo_trans (C.idx b) (C.idx a)).continuousOn.mono hov
    have h3 := (hu a).continuousOn.comp h2 (fun v hv => hv.2.2.2)
    have h4 := (hF.1 (C.idx b)).continuousOn.mono (t := W b a) (fun v hv => hv.2.1)
    exact (h1.mul h3).sub h4
  have hcomp : ∀ a i y, y ∈ (A.chart i).source → y ∈ (A.chart (C.idx a)).source →
      D a (A.pick y) y = A.g (A.kap + la) (A.pick y) i y * D a i y := by
    intro a i y hi ha
    simp only [hD]
    rw [A.g_cocycle _ (A.pick y) i (C.idx a) y (A.mem_pick y) hi ha,
      hF.2 (A.pick y) i y (A.mem_pick y) hi]
    ring
  set f : Fin C.m → Fin C.m → V n → ℝ≥0∞ := fun b a v => ENNReal.ofReal
    (‖D a (C.idx b) ((A.chart (C.idx b)).symm v)‖ ^ 2 *
      Real.exp (-A.ph la (C.idx b) ((A.chart (C.idx b)).symm v))) with hf
  have hk : ∀ b a, ∫⁻ y in (A.chart (C.idx b)).source ∩ A.chart (C.idx b) ⁻¹' W b a,
      ENNReal.ofReal (A.nsq (A.kap + la) (D a) y) ∂A.mu = ∫⁻ v in W b a, f b a v := by
    intro b a
    refine GlobalTheory.T.lintegral_nsq_canonical_add_chart_part n Y ι La A la (C.idx b) (W b a) (D a) (hWo b a).measurableSet
      (fun v hv => hv.2.1) (fun y hy hy' => hcomp a _ y hy ?_)
      ((hDc b a).aemeasurable (hWo b a).measurableSet)
    have := hy'.2.2.1
    rwa [(A.chart (C.idx b)).left_inv hy] at this
  have hWaa : ∀ a, W a a = ball (C.c a) (C.r a) := by
    intro a
    refine Set.inter_eq_left.mpr fun v hv => ⟨hbt a hv, (A.chart _).map_target (hbt a hv), ?_⟩
    show A.chart (C.idx a) ((A.chart (C.idx a)).symm v) ∈ ball (C.c a) (C.r a)
    rwa [(A.chart (C.idx a)).right_inv (hbt a hv)]
  have hE : ∀ b a, ∫⁻ v in W b a, f b a v ≤ ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
      (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
    intro b a
    calc _ = _ := (hk b a).symm
      _ ≤ ∫⁻ y in (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' W a a,
          ENNReal.ofReal (A.nsq (A.kap + la) (D a) y) ∂A.mu := by
        apply lintegral_mono_set
        intro y hy
        rw [hWaa]
        have := hy.2.2.2
        rwa [Set.mem_preimage, (A.chart (C.idx b)).left_inv hy.1] at this
      _ = _ := hk a a
      _ = _ := by
        rw [hWaa]
        refine setLIntegral_congr_fun measurableSet_ball fun v hv => ?_
        have hs := (A.chart (C.idx a)).map_target (hbt a hv)
        have h1 : A.g (A.kap + la) (C.idx a) (C.idx a) ((A.chart (C.idx a)).symm v) = 1 := by
          have h2 := A.g_cocycle (A.kap + la) _ _ _ _ hs hs hs
          have h3 := A.g_ne (A.kap + la) _ _ _ hs hs
          exact (mul_right_eq_self₀.mp h2.symm).resolve_right h3
        simp only [hf, hD]
        rw [h1, one_mul, (A.chart (C.idx a)).right_inv (hbt a hv), norm_sub_rev]
  have hfm : ∀ b a, AEMeasurable ((W b a).indicator (f b a))
      (volume.restrict (ball (C.c b) (C.r b))) := by
    intro b a
    refine AEMeasurable.restrict ?_
    rw [aemeasurable_indicator_iff (hWo b a).measurableSet]
    refine ContinuousOn.aemeasurable ?_ (hWo b a).measurableSet
    have h4 := (A.smooth_ph la (C.idx b)).continuousOn.mono (t := W b a) (fun v hv => hv.2.1)
    exact ENNReal.continuous_ofReal.comp_continuousOn
      (((hDc b a).norm.pow 2).mul (Real.continuous_exp.comp_continuousOn h4.neg))
  have hpt : ∀ b, ∀ v ∈ ball (C.c b) (C.r b), ENNReal.ofReal
      ((∑ j, ‖wdb n j (glue C la u (C.idx b) ∘ (A.chart (C.idx b)).symm) v‖ ^ 2) *
        Real.exp (-A.ph la (C.idx b) ((A.chart (C.idx b)).symm v))) ≤
      ENNReal.ofReal (n * (C.m * B ^ 2)) * ∑ a, (W b a).indicator (f b a) v := by
    intro b v hv
    set e : Fin C.m → ℝ := fun a => (W b a).indicator
      (fun v => ‖D a (C.idx b) ((A.chart (C.idx b)).symm v)‖ ^ 2) v with he
    have he0 : ∀ a, 0 ≤ e a := fun a => Set.indicator_nonneg (fun _ _ => by positivity) _
    have h1 : ∀ j, ‖wdb n j (glue C la u (C.idx b) ∘ (A.chart (C.idx b)).symm) v‖ ^ 2 ≤
        C.m * B ^ 2 * ∑ a, e a := by
      intro j
      rw [GlobalTheory.T.dbar_glueSectionByPartition_eq n Y ι La A C la u (C.idx b) v (F0 (C.idx b) ((A.chart (C.idx b)).symm v))
        j hu (hbt b hv)]
      apply sq_sum_le
      intro a
      by_cases hm : v ∈ W b a
      · simp only [he, Set.indicator_of_mem hm, hD]
        rw [norm_mul, mul_pow]
        gcongr
        exact hB a b j v hv
      · rw [wdb_eq_zero C a (C.idx b) j v (hbt b hv) (fun h => hm ⟨hv, hbt b hv, h⟩)]
        simp only [zero_mul, norm_zero]
        have := he0 a
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
    have h2 : ∑ a, (W b a).indicator (f b a) v = ENNReal.ofReal ((∑ a, e a) *
        Real.exp (-A.ph la (C.idx b) ((A.chart (C.idx b)).symm v))) := by
      rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg
        (fun a _ => mul_nonneg (he0 a) (Real.exp_pos _).le)]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases hm : v ∈ W b a
      · simp only [he, hf, Set.indicator_of_mem hm]
      · simp [he, Set.indicator_of_notMem hm]
    rw [h2, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc]
    apply ENNReal.ofReal_le_ofReal
    gcongr
    calc _ ≤ ∑ _j : Fin n, C.m * B ^ 2 * ∑ a, e a := Finset.sum_le_sum fun j _ => h1 j
      _ = _ := by simp [mul_assoc]
  unfold n1
  calc _ ≤ ∑ _b : Fin C.m, ENNReal.ofReal (n * (C.m * B ^ 2)) * ∑ a,
        ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
        (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
        refine Finset.sum_le_sum fun b _ => ?_
        refine (setLIntegral_mono' measurableSet_ball (hpt b)).trans ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finset_sum' _ (fun a _ => hfm b a)]
        refine mul_le_mul_right (Finset.sum_le_sum fun a _ => ?_) _
        refine le_trans (setLIntegral_le_lintegral _ _) ?_
        rw [lintegral_indicator (hWo b a).measurableSet]
        exact hE b a
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (p := (C.m : ℝ)) (by positivity), ENNReal.ofReal_natCast, mul_assoc]

end GlobalTheory.OTY.GlueEnergy
