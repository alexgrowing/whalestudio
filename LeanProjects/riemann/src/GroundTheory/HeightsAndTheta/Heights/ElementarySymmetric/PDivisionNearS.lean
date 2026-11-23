import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.DivisionNearS
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDivisionNearSDensity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

open DivisionNearS in

theorem DivisionNearS.proof : DivisionNearS.Statement := by
  intro D T X Z φA hD hDT F hFv hfil t ht
  obtain ⟨hF, hFn⟩ := hFv
  set d : Fin X.A.n → X.U → ℝ≥0∞ := fun a x => ENNReal.ofReal (2 ^ D * ‖F a x‖ ^ 2 *
    (∑ i, ‖Z.s i a x‖ ^ 2) ^ (-(t + 1)) *
      Real.exp (-(φA.φ a x + ((T : ℝ) - 1 - t) * fsWeight X.e a x))) with hd
  set n : Fin X.A.n → X.U → ℝ≥0∞ := fun a x => ENNReal.ofReal (2 ^ D * ‖F a x‖ ^ 2 *
    Real.exp (-(φA.φ a x + (T : ℝ) * fsWeight X.e a x))) with hn
  have hnT : chartIntegral X.A n < ⊤ := hFn
  show chartIntegral X.A d < ⊤

  have hcmp : ∀ a x (M : ℝ), 0 ≤ M → (x ∈ (X.A.chart a).source →
      (∑ i, ‖Z.s i a x‖ ^ 2) ^ (-(t + 1)) * (∑ k, ‖X.e k a x‖ ^ 2) ^ (t + 1) ≤ M) →
      d a x ≤ ENNReal.ofReal M * n a x := by
    intro a x M hM hR
    by_cases hx : x ∈ (X.A.chart a).source
    · simp only [hd, hn]
      rw [← ENNReal.ofReal_mul hM]
      apply ENNReal.ofReal_le_ofReal
      rw [dens_eq X φA T t a x hx]
      calc 2 ^ D * ‖F a x‖ ^ 2 * Real.exp (-(φA.φ a x + (T : ℝ) * fsWeight X.e a x)) *
            ((∑ i, ‖Z.s i a x‖ ^ 2) ^ (-(t + 1)) * (∑ k, ‖X.e k a x‖ ^ 2) ^ (t + 1))
          ≤ 2 ^ D * ‖F a x‖ ^ 2 * Real.exp (-(φA.φ a x + (T : ℝ) * fsWeight X.e a x)) * M :=
            mul_le_mul_of_nonneg_left (hR hx) (by positivity)
        _ = _ := by ring
    · have h0 : F a x = 0 := hF.2.2 a x hx
      simp [hd, h0]
  rcases le_or_gt (t + 1) 0 with ht1 | ht1
  ·
    have hr : 0 ≤ rSq Z.c := by unfold rSq; positivity
    have hM : 0 ≤ rSq Z.c ^ (-(t + 1)) := Real.rpow_nonneg hr _
    calc chartIntegral X.A d
        ≤ chartIntegral X.A (fun a x => ENNReal.ofReal (rSq Z.c ^ (-(t + 1))) * n a x) :=
          ExtensionProof.chartIntegral_mono _ fun a x => hcmp a x _ hM fun hx =>
            ratio_le_of_nonpos t _ _ _ ht1 (esum_pos X a x hx) (by positivity) hr
              (ssum_le X Z a x)
      _ = ENNReal.ofReal (rSq Z.c ^ (-(t + 1))) * chartIntegral X.A n :=
          ExtensionProof.chartIntegral_const_mul _ _ ENNReal.ofReal_ne_top _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hnT
  ·
    have hSfin : (zeroSet X.A Z.s).Finite := Z.finite
    choose ε hε K hsub hbd using fun x₀ : zeroSet X.A Z.s =>
      local_bound X Z φA T hDT F hF hfil t ht1 x₀ x₀.2 (chartIdx X.A x₀) rfl
    set W : zeroSet X.A Z.s → Set X.U := fun x₀ => (X.A.chart (chartIdx X.A x₀)).source ∩
      X.A.chart (chartIdx X.A x₀) ⁻¹' Metric.ball (X.A.chart (chartIdx X.A x₀) x₀) (ε x₀) with hW
    have hWo : ∀ x₀, IsOpen (W x₀) := fun x₀ =>
      (X.A.chart _).continuousOn.isOpen_inter_preimage (X.A.chart _).open_source Metric.isOpen_ball
    have hWc : ∀ x₀ : zeroSet X.A Z.s, W x₀ ⊆ (X.A.chart (chartIdx X.A x₀)).source := fun _ _ h => h.1
    have hWimg : ∀ x₀ : zeroSet X.A Z.s, X.A.chart (chartIdx X.A x₀) '' W x₀ ⊆
        Metric.ball (X.A.chart (chartIdx X.A x₀) x₀) (ε x₀) := by
      rintro x₀ _ ⟨y, hy, rfl⟩; exact hy.2
    set V : Set X.U := ⋃ x₀, W x₀ with hV
    have hVo : IsOpen V := isOpen_iUnion hWo
    have hSV : zeroSet X.A Z.s ⊆ V := fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hx⟩, mem_source_chartIdx X.A x, by
        simpa [Metric.mem_ball] using hε ⟨x, hx⟩⟩
    obtain ⟨C, hC⟩ := Z.fl V hVo hSV

    have hoff : ∀ a x, x ∈ (X.A.chart a).source → x ∉ V →
        (∑ i, ‖Z.s i a x‖ ^ 2) ^ (-(t + 1)) * (∑ k, ‖X.e k a x‖ ^ 2) ^ (t + 1) ≤
          |C| ^ (t + 1) := by
      intro a x hx hxV
      have hc' := mem_source_chartIdx X.A x
      have h1 : ∑ k, ‖X.e k (chartIdx X.A x) x‖ ^ 2 ≤
          C * ∑ i, ‖Z.s i (chartIdx X.A x) x‖ ^ 2 := hC x hxV
      have hnz : x ∉ zeroSet X.A Z.s := fun h => hxV (hSV h)
      have hG : 0 < ‖X.L.g a (chartIdx X.A x) x‖ ^ 2 := by
        have := X.L.ne_zero a (chartIdx X.A x) x ⟨hx, hc'⟩; positivity
      have hSpos : 0 < ∑ i, ‖Z.s i a x‖ ^ 2 := by
        simp only [zeroSet, mem_ofPred_eq, not_forall] at hnz
        obtain ⟨i, hi⟩ := hnz
        have hne : Z.s i a x ≠ 0 := by
          rw [s_transform X Z i a (chartIdx X.A x) x ⟨hx, hc'⟩]
          exact mul_ne_zero (X.L.ne_zero a _ x ⟨hx, hc'⟩) hi
        exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum
          (f := fun i => ‖Z.s i a x‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i))
      have hSE : ∑ k, ‖X.e k a x‖ ^ 2 ≤ |C| * ∑ i, ‖Z.s i a x‖ ^ 2 := by
        rw [esum_transform X a (chartIdx X.A x) x ⟨hx, hc'⟩,
          ssum_transform X Z a (chartIdx X.A x) x ⟨hx, hc'⟩]
        have h2 : C * ∑ i, ‖Z.s i (chartIdx X.A x) x‖ ^ 2 ≤
            |C| * ∑ i, ‖Z.s i (chartIdx X.A x) x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        calc ‖X.L.g a (chartIdx X.A x) x‖ ^ 2 * ∑ k, ‖X.e k (chartIdx X.A x) x‖ ^ 2
            ≤ ‖X.L.g a (chartIdx X.A x) x‖ ^ 2 * (|C| * ∑ i, ‖Z.s i (chartIdx X.A x) x‖ ^ 2) :=
              mul_le_mul_of_nonneg_left (h1.trans h2) hG.le
          _ = _ := by ring
      exact ratio_le_of_nonneg t _ _ _ ht1.le (esum_pos X a x hx) hSpos hSE

    have htr : ∀ x₀ : zeroSet X.A Z.s, ∀ a, ∀ p ∈ (X.A.chart a).source ∩ W x₀,
        d a p = ENNReal.ofReal (‖jac X.A a (chartIdx X.A x₀) p‖ ^ 2) * d (chartIdx X.A x₀) p := by
      intro x₀ a p hp
      simp only [hd]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      exact dens_transform X Z φA T t F hF a (chartIdx X.A x₀) p ⟨hp.1, hp.2.1⟩
    have hexp : ∀ x₀ : zeroSet X.A Z.s, ∫⁻ w in Metric.ball (X.A.chart (chartIdx X.A x₀) x₀) (ε x₀),
        ENNReal.ofReal (K x₀ * ‖w - X.A.chart (chartIdx X.A x₀) x₀‖ ^
          (2 * ((T : ℝ) - D) - 2 * (t + 1))) < ⊤ := by
      intro x₀
      have ha : -(2 * D : ℝ) < 2 * ((T : ℝ) - D) - 2 * (t + 1) := by linarith
      calc _ ≤ ∫⁻ w in Metric.ball (X.A.chart (chartIdx X.A x₀) x₀) (ε x₀),
            ENNReal.ofReal |K x₀| * ENNReal.ofReal (‖w - X.A.chart (chartIdx X.A x₀) x₀‖ ^
              (2 * ((T : ℝ) - D) - 2 * (t + 1))) := by
            refine lintegral_mono fun w => ?_
            rw [← ENNReal.ofReal_mul (abs_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _)
              (Real.rpow_nonneg (norm_nonneg _) _))
        _ = ENNReal.ofReal |K x₀| * ∫⁻ w in Metric.ball (X.A.chart (chartIdx X.A x₀) x₀) (ε x₀),
            ENNReal.ofReal (‖w - X.A.chart (chartIdx X.A x₀) x₀‖ ^
              (2 * ((T : ℝ) - D) - 2 * (t + 1))) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (lintegral_ball_rpow_lt_top hD _ _ _ ha)
    have : Finite (zeroSet X.A Z.s) := hSfin.to_subtype
    have : Fintype (zeroSet X.A Z.s) := Fintype.ofFinite _
    unfold chartIntegral
    refine ENNReal.sum_lt_top.mpr fun j _ => ?_
    set O := (X.A.chart j).target ∩ (X.A.chart j).symm ⁻¹' V with hOdef
    have hO : IsOpen O :=
      (X.A.chart j).continuousOn_symm.isOpen_inter_preimage (X.A.chart j).open_target hVo
    rw [← inter_union_sdiff (piece X.A j) O]
    refine (lintegral_union_le _ _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    ·
      have hcov : piece X.A j ∩ O ⊆
          ⋃ x₀, piece X.A j ∩ ((X.A.chart j).target ∩ (X.A.chart j).symm ⁻¹' W x₀) := by
        rintro y ⟨hp, hyt, hyV⟩
        obtain ⟨x₀, hx₀⟩ := mem_iUnion.mp hyV
        exact mem_iUnion.mpr ⟨x₀, hp, hyt, hx₀⟩
      refine (lintegral_mono_set hcov).trans_lt ((lintegral_iUnion_le _ _).trans_lt ?_)
      rw [tsum_fintype]
      refine ENNReal.sum_lt_top.mpr fun x₀ _ => ?_
      refine (setLIntegral_piece_le_chart X.A d (chartIdx X.A x₀) (W x₀) (hWo x₀) (hWc x₀)
        (htr x₀) j).trans_lt ?_
      refine (lintegral_mono_set (hWimg x₀)).trans_lt ?_
      exact (setLIntegral_mono' measurableSet_ball fun w hw => hbd x₀ w hw).trans_lt (hexp x₀)
    ·
      have hmeas : MeasurableSet (piece X.A j \ O) :=
        (ExtensionProof.measurableSet_piece X.A j).diff hO.measurableSet
      have hM : (0 : ℝ) ≤ |C| ^ (t + 1) := Real.rpow_nonneg (abs_nonneg _) _
      refine (setLIntegral_mono' hmeas (g := fun y => ENNReal.ofReal (|C| ^ (t + 1)) *
        n j ((X.A.chart j).symm y)) fun y hy => ?_).trans_lt ?_
      · have hyt : y ∈ (X.A.chart j).target := hy.1.1
        have hyV : (X.A.chart j).symm y ∉ V := fun h => hy.2 ⟨hyt, h⟩
        exact hcmp j _ _ hM fun hx => hoff j _ hx hyV
      · refine (lintegral_mono_set sdiff_subset).trans_lt ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt ?_ hnT)
        exact Finset.single_le_sum (f := fun k => ∫⁻ y in piece X.A k, n k ((X.A.chart k).symm y))
          (fun _ _ => by simp) (Finset.mem_univ j)

end

end GroundTheory.Heights₂.Heights.EffectiveHS
