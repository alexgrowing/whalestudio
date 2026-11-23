import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousInvLeadingBlockEntry
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeLoc
import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.PoleValue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

variable {X : Data E r} {x0 x1 : Frame X.Ψ r}

theorem dmin_cpt_eq (h0 : IsOrth X x0) (h1 : IsOrth X x1) (z : V (nd X)) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (cpt X x1 z) τ i = dmin X.Gm (cpt X x0 z) τ i := by
  have e : ∀ x : Frame X.Ψ r, mat (cpt X x z) τ = mat x τ * mat (nmat X z) τ := fun _ => rfl
  unfold dmin
  rw [e, e, FrameDegreeData.gram_mul, FrameDegreeData.gram_mul, h0 τ, h1 τ]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} {x0 x1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} in
private theorem det_mat_cpt_ne_zero_iff_det_nmat (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) :
    (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) τ).det ≠ 0 ↔ (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) τ).det ≠ 0 := by
  have hx := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.orth_mem_dom X x0 h
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG at hx
  have hdet := (Set.mem_setOf_eq ▸ hx) τ |>.1
  rw [show _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) τ from rfl,
    Matrix.det_mul]
  exact ⟨fun hne ↦ right_ne_zero_of_mul hne, fun hne ↦ mul_ne_zero hdet hne⟩

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} {x0 x1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} in
private theorem dmin_cpt_eq_of_isOrth (h0 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) (h1 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x1)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x1 z) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) τ i := by
  have g0 : ∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ) =
      Matrix.diagonal fun a : Fin r ↦ ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑a : ℝ) : ℂ) := h0
  have g1 : ∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x1 τ) =
      Matrix.diagonal fun a : Fin r ↦ ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑a : ℝ) : ℂ) := h1
  have hmat : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r,
      _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) τ := fun _ ↦ rfl
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rw [hmat, hmat, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, g0, g1]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} {x0 x1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} in
theorem _root_.GlobalTheory.Up.PoleValue.OmF_eq (h0 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) (h1 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x1) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x1 = _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0 := by
  ext z
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG
  simp only [Set.mem_setOf_eq, det_mat_cpt_ne_zero_iff_det_nmat h0, det_mat_cpt_ne_zero_iff_det_nmat h1,
    dmin_cpt_eq_of_isOrth h0 h1]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} {x0 x1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} in
theorem _root_.GlobalTheory.Up.PoleValue.rhF_eq (h0 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) (h1 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x1) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF X x1 = _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF X x0 := by
  funext z
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF
  simp only [dmin_cpt_eq_of_isOrth h0 h1]

theorem densF_eq (h0 : IsOrth X x0) (h1 : IsOrth X x1) : densF X x1 = densF X x0 := by
  funext z
  simp only [densF, dmin_cpt_eq h0 h1]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} {x0 x1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} in
theorem _root_.GlobalTheory.Up.PoleValue.muF_eq (h0 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) (h1 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x1) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x1 = _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF
  rw [_root_.GlobalTheory.Up.PoleValue.OmF_eq h0 h1]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF
  simp only [dmin_cpt_eq_of_isOrth h0 h1]

end GlobalTheory.Up.PoleValue

namespace GlobalTheory.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.Up.polePoint_holds : _root_.GlobalTheory.Up.PolePoint (E := E) := by
  unfold _root_.GlobalTheory.Up.PolePoint
  intro r X ρ c hdim hρ hc
  set d := _root_.GlobalTheory.Up.dimX X with hd
  by_cases hex : ∃ x0, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0
  swap
  · exact ⟨1, one_pos, fun x1 h1 ↦ absurd ⟨x1, h1⟩ hex⟩
  obtain ⟨x0, h0⟩ := hex
  obtain ⟨ε, hε, m, hm, hdens⟩ : ∃ ε > 0, ∃ m > 0,
      ∀ w ∈ Metric.ball (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) ε, m ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0 w := by
    have hc' : ∀ τ i, Continuous fun w ↦ _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 w) τ i :=
      fun τ i ↦ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.dmin_cpt_cd X x0 τ i).continuous
    have hne : ∀ τ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 0) τ i ≠ 0 := by
      intro τ i
      rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero]
      exact _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.dmin_ne_zero X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.orth_mem_dom X x0 h0) τ i
    have hcont : ContinuousAt (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0) 0 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF
      refine tendsto_finset_prod _ fun τ _ ↦ tendsto_finset_prod _ fun i _ ↦ ?_
      exact ((hc' τ _).continuousAt.norm).zpow₀ _ (Or.inl (norm_ne_zero_iff.2 (hne τ _)))
    have hpos : 0 < _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0 0 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF
      exact Finset.prod_pos fun τ _ ↦ Finset.prod_pos fun i _ ↦
        zpow_pos (norm_pos_iff.2 (hne τ _)) _
    obtain ⟨ε, hε, hball⟩ :=
      Metric.eventually_nhds_iff_ball.1 (hcont.eventually (lt_mem_nhds (half_lt_self hpos)))
    exact ⟨ε, hε, _, half_pos hpos, fun w hw ↦ (hball w hw).le⟩
  obtain ⟨hnonneg, ρ1, C, hρ1, hquad⟩ := _root_.GlobalTheory.SharpGradient.rhF_sharp_gradient r X x0 h0
  obtain ⟨L, hLsurj, hLnorm⟩ : ∃ L : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) →L[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V d,
      Function.Surjective L ∧ ∀ z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖L z‖ ^ 2 =
        ∑ e : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X, if (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ) then
          ‖z.ofLp ((Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X)) e)‖ ^ 2 else 0 := by
    let σ := Fintype.equivFinOfCardEq (_root_.GlobalTheory.Up.card_mixedEnt X)
    let f : Fin d → Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) := fun k ↦ Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) (σ.symm k).1
    have hf : Function.Injective f := fun a b hab ↦
      σ.symm.injective (Subtype.ext ((Fintype.equivFin _).injective hab))
    let L₀ : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V d :=
      (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).symm.toLinearMap ∘ₗ LinearMap.funLeft ℂ ℂ f ∘ₗ
        (WithLp.linearEquiv 2 ℂ (Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ)).toLinearMap
    refine ⟨LinearMap.toContinuousLinearMap L₀, ?_, ?_⟩
    · intro y
      obtain ⟨g, hg⟩ := LinearMap.funLeft_surjective_of_injective ℂ ℂ f hf
        (WithLp.linearEquiv 2 ℂ (Fin d → ℂ) y)
      refine ⟨(WithLp.linearEquiv 2 ℂ (Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ)).symm g, ?_⟩
      simp [L₀, hg]
    · intro z
      rw [EuclideanSpace.norm_sq_eq]
      change ∑ k, ‖z.ofLp ((Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X)) (σ.symm k).1)‖ ^ 2 = _
      rw [← Finset.sum_filter]
      rw [Equiv.sum_comp σ.symm (fun x ↦ ‖z.ofLp ((Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X)) x.1)‖ ^ 2)]
      rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  set ρ' := min ρ (min ρ1 ε) with hρ'
  have hρ'pos : 0 < ρ' := lt_min hρ (lt_min hρ1 hε)
  obtain ⟨δ', hδ', hball, hblow⟩ := _root_.ReciprocityTheory.L2DbarEstimates.Y.ap_local_blowup (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) d hdim _root_.ReciprocityTheory.L2DbarEstimates.mv (_root_.ReciprocityTheory.L2DbarEstimates.mvInt d)
    (Metric.ball 0 ρ') Metric.isOpen_ball L L.differentiableOn 0
    (Metric.mem_ball_self hρ'pos) (map_zero L) (by rw [L.fderiv]; exact hLsurj)
  set K := max C 0 + 1 with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨τ0, hτ0, hτ⟩ := hblow (K ^ (d : ℝ) / (c * m))
  refine ⟨τ0, hτ0, fun x1 h1 δ hδ hδτ u hu ↦ ?_⟩
  rw [_root_.GlobalTheory.Up.PoleValue.OmF_eq h0 h1] at hu
  rw [_root_.GlobalTheory.Up.PoleValue.rhF_eq h0 h1,
    _root_.GlobalTheory.Up.PoleValue.muF_eq h0 h1]
  have hsub : Metric.ball (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) δ' ⊆ Metric.ball 0 ρ' :=
    Metric.ball_subset_closedBall.trans hball
  have hmem : ∀ v ∈ Metric.ball (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) δ',
      ‖v‖ < ρ ∧ ‖v‖ < ρ1 ∧ ‖v‖ < ε := by
    intro v hv
    have h := hsub hv
    rw [Metric.mem_ball, dist_zero_right] at h
    exact ⟨h.trans_le (min_le_left _ _), h.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
      h.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hu' : DifferentiableOn ℂ u (Metric.ball 0 δ') := by
    refine hu.mono fun v hv ↦ ⟨?_, (hquad v (hmem v hv).2.1).1⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact (hmem v hv).1
  have key := hτ δ hδ hδτ u hu'
  have hμ : ENNReal.ofReal m • volume.restrict (Metric.ball (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) δ') ≤
      (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0).restrict (Metric.ball 0 ρ) := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs, Measure.restrict_apply hs]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF
    rw [withDensity_apply _ (hs.inter measurableSet_ball),
      Measure.restrict_restrict (hs.inter measurableSet_ball)]
    calc ENNReal.ofReal m * volume (s ∩ Metric.ball 0 δ')
        = ∫⁻ _ in s ∩ Metric.ball 0 δ', ENNReal.ofReal m := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ a in s ∩ Metric.ball 0 δ', ENNReal.ofReal (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0 a) :=
          setLIntegral_mono' (hs.inter measurableSet_ball) fun a ha ↦
            ENNReal.ofReal_le_ofReal (hdens a (by
              rw [Metric.mem_ball, dist_zero_right]; exact (hmem a ha.2).2.2))
      _ ≤ _ := by
          refine lintegral_mono_set fun a ha ↦ Set.mem_inter (Set.mem_inter ha.1 ?_)
            (hquad a (hmem a ha.2).2.1).1
          rw [Metric.mem_ball, dist_zero_right]
          exact (hmem a ha.2).1
  have hpt : ∀ v ∈ Metric.ball (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) δ',
      ENNReal.ofReal (K ^ (-(d : ℝ))) *
          ENNReal.ofReal (‖u v‖ ^ 2 * max (‖L v‖ ^ 2) δ ^ (-(d : ℝ))) ≤
        ENNReal.ofReal (‖u v‖ ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF X x0 v + δ) ^ (-(d : ℝ))) := by
    intro v hv
    have hvmem := (hquad v (hmem v hv).2.1).1
    have hw0 : 0 ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF X x0 v := (hnonneg v hvmem).1
    have hq := (hquad v (hmem v hv).2.1).2
    rw [← hLnorm v] at hq
    have ht : 0 ≤ ‖L v‖ ^ 2 := by positivity
    have hM : 0 < max (‖L v‖ ^ 2) δ := lt_max_of_lt_right hδ
    have hle : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF X x0 v + δ ≤ K * max (‖L v‖ ^ 2) δ := by
      have h1 : C * ‖L v‖ ^ 2 ≤ max C 0 * max (‖L v‖ ^ 2) δ :=
        mul_le_mul (le_max_left _ _) (le_max_left _ _) ht (le_max_right _ _)
      rw [hK, add_mul, one_mul]
      linarith [le_max_right (‖L v‖ ^ 2) δ]
    have hpow : (K * max (‖L v‖ ^ 2) δ) ^ (-(d : ℝ)) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF X x0 v + δ) ^ (-(d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (add_pos_of_nonneg_of_pos hw0 hδ) hle
        (neg_nonpos.2 (Nat.cast_nonneg _))
    rw [Real.mul_rpow hKpos.le hM.le] at hpow
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hKpos.le _)]
    apply ENNReal.ofReal_le_ofReal
    calc K ^ (-(d : ℝ)) * (‖u v‖ ^ 2 * max (‖L v‖ ^ 2) δ ^ (-(d : ℝ)))
        = ‖u v‖ ^ 2 * (K ^ (-(d : ℝ)) * max (‖L v‖ ^ 2) δ ^ (-(d : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  calc ENNReal.ofReal (‖u 0‖ ^ 2)
      = ENNReal.ofReal c * (ENNReal.ofReal m * (ENNReal.ofReal (K ^ (-(d : ℝ))) *
          ENNReal.ofReal (K ^ (d : ℝ) / (c * m) * ‖u 0‖ ^ 2))) := by
        rw [← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul]
        · congr 1
          rw [Real.rpow_neg hKpos.le]
          have hKd : 0 < K ^ (d : ℝ) := Real.rpow_pos_of_pos hKpos _
          field_simp
        all_goals positivity
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal m * (ENNReal.ofReal (K ^ (-(d : ℝ))) *
          ∫⁻ v in Metric.ball 0 δ', ENNReal.ofReal (‖u v‖ ^ 2 * max (‖L v‖ ^ 2) δ ^ (-(d : ℝ))))) := by
        gcongr
    _ = ENNReal.ofReal c * (ENNReal.ofReal m * ∫⁻ v in Metric.ball 0 δ',
          ENNReal.ofReal (K ^ (-(d : ℝ))) *
            ENNReal.ofReal (‖u v‖ ^ 2 * max (‖L v‖ ^ 2) δ ^ (-(d : ℝ)))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal m * ∫⁻ v in Metric.ball 0 δ',
          ENNReal.ofReal (‖u v‖ ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF X x0 v + δ) ^ (-(d : ℝ)))) := by
        gcongr ENNReal.ofReal c * (ENNReal.ofReal m * ?_)
        exact setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt
    _ = ENNReal.ofReal c * ∫⁻ v, ENNReal.ofReal (‖u v‖ ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF X x0 v + δ) ^ (-(d : ℝ)))
          ∂(ENNReal.ofReal m • volume.restrict (Metric.ball (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) δ')) := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ _ := by
        gcongr ENNReal.ofReal c * ?_
        exact lintegral_mono' hμ le_rfl

end GlobalTheory.Up
