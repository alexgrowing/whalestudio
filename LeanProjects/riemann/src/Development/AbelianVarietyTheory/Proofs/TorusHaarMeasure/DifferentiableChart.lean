import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfL
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfO
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.InterpolationPeaks
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneAddInvFirstMinimumLeOfMajorants
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeviFormWeightMetricOrthonormalDiagonal
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.BorelDiagNeZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PhlaBlockWtCpt
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SqLeQyOfLeFirstMinimum
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsInvariantGe
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CfwMOfExtraBounds

namespace GlobalTheory.InterpCompare

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory Topology
open scoped ContDiff ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem continuousAt_levi {n : ℕ} {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ ∞ f x) (ξ : Fin n → ℂ) :
    ContinuousAt (fun y => (leviV n (fun w => ((f w : ℝ) : ℂ)) y ξ).re) x := by
  have h2 : ContDiffAt ℝ 2 f x := hf.of_le HE.two_le_inf
  have hd : ContinuousAt (fderiv ℝ (fderiv ℝ f)) x :=
    ((h2.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  set u : V n := ∑ k, ((ξ k).re • bas n k + (ξ k).im • Complex.I • bas n k)
  set v : V n := ∑ k, ((ξ k).re • Complex.I • bas n k - (ξ k).im • bas n k)
  have hc : ContinuousAt (fun y => (fderiv ℝ (fderiv ℝ f) y u u + fderiv ℝ (fderiv ℝ f) y v v) / 4) x :=
    (((hd.clm_apply continuousAt_const).clm_apply continuousAt_const).add
      ((hd.clm_apply continuousAt_const).clm_apply continuousAt_const)).div_const 4
  refine hc.congr ?_
  filter_upwards [h2.eventually (by simp)] with y hy
  rw [← Y.LocalMaximumSecondDerivative.leviV_re_eq hy ξ]
  ring

theorem differentiable_chart (X : Data E r) (x0 : Frame X.Ψ r) : Differentiable ℂ (cpt X x0) :=
  IW.cpt_diff X x0

theorem levi_transport (X : Data E r) {x0 x1 : Frame X.Ψ r} (ho : IsOrth X x1) {z z1 : V (nd X)}
    (hz : z ∈ OmF X x0) (hz1 : z1 ∈ OmF X x1) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (hxb : cpt X x0 z = rmul (cpt X x1 z1) b) (ξ : Fin (nd X) → ℂ) :
    ∃ ξ' : Fin (nd X) → ℂ, (∀ la, leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 z1 ξ') ∧
      ∀ ψ : Frame X.Ψ r → ℝ, IsInvFn X ψ → ContDiffAt ℝ 2 (fun w => ψ (cpt X x1 w)) z1 →
        leviM X ψ x0 z ξ = leviM X ψ x1 z1 ξ' := by
  obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, hbd, hsplit, hinv⟩ := lu_holds r X x1 ho
  have h0 := hinv z1 hz1 b hb
  rw [← hxb] at h0
  have hcd := differentiable_chart X x0
  set U : Set (V (nd X)) := {w | cpt X x0 w ∈ X.dom ∧ Δ (cpt X x0 w) ≠ 0} with hUdef
  have hU : IsOpen U :=
    (ExF.isOpen_OmF X x0).inter (isOpen_compl_singleton.preimage (hΔ.comp hcd).continuous)
  have hzU : z ∈ U := ⟨hz, h0.1⟩
  set Φ : V (nd X) → V (nd X) := fun w => zOf (cpt X x0 w) with hΦdef
  set bf : V (nd X) → Frame X.Ψ r := fun w => bOf (cpt X x0 w) with hbfdef
  have hΦ : DifferentiableOn ℂ Φ U := hzd.comp hcd.differentiableOn fun w hw => hw
  have hbf : DifferentiableOn ℂ bf U := hbd.comp hcd.differentiableOn fun w hw => hw
  have hΦz : Φ z = z1 := h0.2.1
  have hΦ2 : ContDiffOn ℂ 2 Φ U := by
    rw [contDiffOn_piLp]
    intro i
    exact (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ U hU
      ((differentiableOn_piLp 2).1 hΦ i)).of_le HE.two_le_inf
  refine ⟨fun k => (fderiv ℂ Φ z (WithLp.toLp 2 ξ)).ofLp k, fun la => ?_, fun ψ hψ hψs => ?_⟩
  · have hch : DifferentiableOn ℂ (fun w => bchar la (bf w)) U := by
      classical
      intro w hw
      unfold bchar
      refine DifferentiableAt.differentiableWithinAt ?_
      refine (HasFDerivAt.finsetProd (g' := fun τ => fderiv ℂ (fun w => ∏ i, bf w τ i i ^ la τ i) w)
        fun τ _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
      refine (HasFDerivAt.finsetProd (g' := fun i => fderiv ℂ (fun w => bf w τ i i ^ la τ i) w)
        fun i _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
      have hw' : DifferentiableAt ℂ bf w := hbf.differentiableAt (hU.mem_nhds hw)
      have hi : DifferentiableAt ℂ (fun w => bf w τ i i) w :=
        differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hw' τ) i) i
      have hzp : DifferentiableAt ℂ (fun t : ℂ => t ^ la τ i) (bf w τ i i) :=
        differentiableAt_zpow.2
          (Or.inl (GlobalTheory.LeviTransfer.borel_diag_ne_zero (hsplit _ hw.1 hw.2).2.1 τ i))
      exact DifferentiableAt.comp (g := fun t : ℂ => t ^ la τ i) w hzp hi
    have hchz : ContDiffAt ℂ 2 (fun w => bchar la (bf w)) z :=
      (HE.contDiffAt_of_punct hU hch hzU).of_le HE.two_le_inf
    have hne : bchar la (bf z) ≠ 0 := IW.bchar_ne_zero X (hsplit _ hz h0.1).2.1 _
    have hev : (fun w => ((phla X la (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
        fun w => ((phla X la (cpt X x1 (Φ w)) + Real.log (Complex.normSq (bchar la (bf w))) : ℝ) : ℂ) := by
      filter_upwards [hU.mem_nhds hzU] with w hw
      obtain ⟨h1, h2, h3⟩ := hsplit _ hw.1 hw.2
      rw [← GlobalTheory.LeviTransfer.metric_rmul normFactor_rightBorel_holds X la h1 h2, ← h3]
    have hg : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 w)) (Φ z) := by
      rw [hΦz]
      exact (IW.phla_cpt_cdAt X x1 hz1 la).of_le HE.two_le_inf
    have h1 : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 (Φ w))) z :=
      hg.comp z ((hΦ2.contDiffAt (hU.mem_nhds hzU)).restrict_scalars ℝ)
    have h2 : ContDiffAt ℝ 2 (fun w => Real.log (Complex.normSq (bchar la (bf w)))) z :=
      (HE.normSq_contDiffAt hchz).log (Complex.normSq_pos.2 hne).ne'
    have hgC : ContDiffAt ℝ 2 (fun w => ((phla X la (cpt X x1 w) : ℝ) : ℂ)) (Φ z) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp _ hg
    have hc := RGF.gc_leviV_comp _ _ _ Φ U hU z hzU hΦ2 hgC ξ
    rw [hΦz] at hc
    unfold leviM
    rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 h2,
      HE.levi_logNormSq_zero_at _ z hchz hne ξ, add_zero]
    exact congrArg Complex.re hc
  · have hev : (fun w => ((ψ (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
        fun w => ((ψ (cpt X x1 (Φ w)) : ℝ) : ℂ) := by
      filter_upwards [hU.mem_nhds hzU] with w hw
      obtain ⟨h1, h2, h3⟩ := hsplit _ hw.1 hw.2
      have := hψ 1 X.Γ.one_mem _ h1 _ h2
      rw [IW.lact_one, ← h3] at this
      rw [this]
    have hgC : ContDiffAt ℝ 2 (fun w => ((ψ (cpt X x1 w) : ℝ) : ℂ)) (Φ z) := by
      rw [hΦz]
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ hψs
    have hc := RGF.gc_leviV_comp _ _ _ Φ U hU z hzU hΦ2 hgC ξ
    rw [hΦz] at hc
    unfold leviM
    rw [leviV_congr hev]
    exact congrArg Complex.re hc

theorem frequently_overlap (X : Data E r) {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0) (h1 : IsOrth X x1)
    {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ∃ᶠ w in 𝓝 z, w ∈ OmF X x0 ∧ ∃ z1 ∈ OmF X x1, ∃ b ∈ Bor X.Ψ r, cpt X x0 w = rmul (cpt X x1 z1) b := by
  obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, -, hsplit, hinv⟩ := lu_holds r X x0 h0
  obtain ⟨Δ', zOf', bOf', -, hden, -, -, hsplit', -⟩ := lu_holds r X x1 h1
  have hone := hinv z hz _ (ExtFPf.oneF_mem X)
  rw [ExtFPf.rmul_oneF] at hone
  have hU : IsOpen {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
    (IW.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  have hmem : cpt X x0 z ∈ {y | y ∈ X.dom ∧ Δ y ≠ 0} := ⟨hz, hone.1⟩
  have hc : Filter.Tendsto zOf (𝓝 (cpt X x0 z)) (𝓝 z) := by
    have := (hzd.continuousOn.continuousAt (hU.mem_nhds hmem)).tendsto
    rwa [hone.2.1] at this
  refine hc.frequently ?_
  have hfr : ∃ᶠ y in 𝓝 (cpt X x0 z), Δ' y ≠ 0 := by
    rw [Metric.nhds_basis_ball.frequently_iff]
    intro ε hε
    exact hden _ hz ε hε
  refine (hfr.and_eventually (hU.mem_nhds hmem)).mono ?_
  rintro y ⟨hy', hy, hyΔ⟩
  obtain ⟨a1, a2, a3⟩ := hsplit y hy hyΔ
  obtain ⟨b1, b2, b3⟩ := hsplit' y hy hy'
  refine ⟨a1, _, b1, IW.bmul X (bOf' y) (IW.binv X (bOf y)), IW.bmul_mem X b2 (IW.binv_mem X a2), ?_⟩
  rw [← IW.rmul_rmul, ← b3]
  have := IW.rmul_binv X (cpt X x0 (zOf y)) a2
  rw [← a3] at this
  exact this.symm

theorem ineq_transport (X : Data E r) {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0) (h1 : IsOrth X x1)
    (la la' : Wt X.Ψ r) (c : ℝ) {ψ : Frame X.Ψ r → ℝ} (hψ : IsInvFn X ψ)
    (hs : ∀ x, IsOrth X x → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x z)) (OmF X x))
    (h : ∀ z ∈ OmF X x1, ∀ ξ, c * leviM X (phla X la') x1 z ξ ≤ leviM X (phla X la) x1 z ξ + leviM X ψ x1 z ξ) :
    ∀ z ∈ OmF X x0, ∀ ξ, c * leviM X (phla X la') x0 z ξ ≤ leviM X (phla X la) x0 z ξ + leviM X ψ x0 z ξ := by
  intro z hz ξ
  have hfr : ∃ᶠ w in 𝓝 z, c * leviM X (phla X la') x0 w ξ ≤
      leviM X (phla X la) x0 w ξ + leviM X ψ x0 w ξ := by
    refine (frequently_overlap X h0 h1 hz).mono ?_
    rintro w ⟨hw, z1, hz1, b, hb, e⟩
    obtain ⟨ξ', e1, e2⟩ := levi_transport X h1 hw hz1 hb e ξ
    rw [e1, e1, e2 ψ hψ (((hs x1 h1).contDiffAt ((ExF.isOpen_OmF X x1).mem_nhds hz1)).of_le HE.two_le_inf)]
    exact h z1 hz1 ξ'
  have c1 := continuousAt_levi (IW.phla_cpt_cdAt X x0 hz la') ξ
  have c2 := continuousAt_levi (IW.phla_cpt_cdAt X x0 hz la) ξ
  have c3 := continuousAt_levi ((hs x0 h0).contDiffAt ((ExF.isOpen_OmF X x0).mem_nhds hz)) ξ
  by_contra hn
  have := (c2.add c3).eventually_lt ((continuousAt_const (y := c)).mul c1) (not_le.1 hn)
  obtain ⟨w, a, b⟩ := (hfr.and_eventually this).exists
  exact absurd a (not_le.2 b)

end GlobalTheory.InterpCompare
