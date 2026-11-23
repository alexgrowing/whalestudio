import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsSelectForms

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ProperImmersionPoint

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pnorm_sq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : X.pnorm la P x ^ 2 = ‖P x‖ ^ 2 * Real.exp (-phla X la x) := by
  have hn := FlowCoefficientBounds.nfac_pos X hx la
  have e : X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl
  have e2 : -phla X la x = ((2 : ℕ) : ℝ) * Real.log (X.nfac la x) := by
    unfold phla; push_cast; ring
  rw [e, e2, Real.exp_nat_mul, Real.exp_log hn, mul_pow]

theorem pnorm_contOn {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ}
    (hP : DifferentiableOn ℂ P X.dom) : ContinuousOn (X.pnorm la P) X.dom :=
  hP.continuousOn.norm.mul (ExtFPf.nfac_contOn X la)

theorem phla_lin {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (L eW : Wt X.Ψ r) (a : ℕ) :
    phla X (a • L - eW) x = a * phla X L x - phla X eW x := by
  rw [IW.phla_eq X hx, IW.phla_eq X hx, IW.phla_eq X hx, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem cpt_differentiable {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) :
    Differentiable ℂ (cpt X x0) :=
  differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b =>
    (IW.cpt_entry_cd X x0 τ a b).differentiable (by simp)

noncomputable def ratio {r : ℕ} (X : Data E r) (L eW : Wt X.Ψ r) {N : ℕ} (a : ℕ)
    (w : Fin N → Frame X.Ψ r → ℂ) (et : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ :=
  X.pnorm eW et x ^ 2 / (∑ k, X.pnorm L (w k) x ^ 2) ^ a

theorem sum_pnorm_sq {r : ℕ} {X : Data E r} (L : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∑ k, X.pnorm L (w k) x ^ 2 = (∑ k, ‖w k x‖ ^ 2) * Real.exp (-phla X L x) := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => pnorm_sq X _ _ hx

theorem sum_norm_pos {r : ℕ} {X : Data E r} {N : ℕ} {w : Fin N → Frame X.Ψ r → ℂ}
    (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < ∑ k, ‖w k x‖ ^ 2 := by
  obtain ⟨k, hk⟩ := hnz x hx
  exact Finset.sum_pos' (fun j _ => by positivity)
    ⟨k, Finset.mem_univ k, pow_pos (norm_pos_iff.2 hk) 2⟩

theorem sum_pnorm_pos {r : ℕ} {X : Data E r} {L : Wt X.Ψ r} {N : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ}
    (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < ∑ k, X.pnorm L (w k) x ^ 2 := by
  rw [sum_pnorm_sq L w hx]
  exact mul_pos (sum_norm_pos hnz hx) (Real.exp_pos _)

theorem ratio_pos {r : ℕ} {X : Data E r} {L eW : Wt X.Ψ r} {N a : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ} {et : Frame X.Ψ r → ℂ}
    (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h : et x ≠ 0) : 0 < ratio X L eW a w et x := by
  refine div_pos ?_ (pow_pos (sum_pnorm_pos hnz hx) _)
  rw [pnorm_sq X _ _ hx]
  exact mul_pos (pow_pos (norm_pos_iff.2 h) 2) (Real.exp_pos _)

theorem ratio_contOn {r : ℕ} {X : Data E r} {L eW : Wt X.Ψ r} {N a : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ} {et : Frame X.Ψ r → ℂ}
    (hw : ∀ k, X.IsSec L (w k)) (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) (het : X.IsSec eW et) :
    ContinuousOn (ratio X L eW a w et) X.dom := by
  refine ContinuousOn.div ((pnorm_contOn X _ het.1).pow 2) (ContinuousOn.pow ?_ _)
    fun x hx => (pow_pos (sum_pnorm_pos hnz hx) _).ne'
  exact continuousOn_finsetSum _ fun k _ => (pnorm_contOn X _ (hw k).1).pow 2

theorem exists_max {r : ℕ} {X : Data E r} {L eW : Wt X.Ψ r} {N a : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ} {et : Frame X.Ψ r → ℂ}
    (hw : ∀ k, X.IsSec L (w k)) (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) (het : X.IsSec eW et)
    (hne : ∃ x ∈ X.dom, et x ≠ 0)
    (hprop : ∀ δ : ℝ, 0 < δ → ∃ C : Set (Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom,
      δ * (∑ k, X.pnorm L (w k) x ^ 2) ^ a ≤ X.pnorm eW et x ^ 2 →
        ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C) :
    ∃ x ∈ X.dom, et x ≠ 0 ∧ ∀ y ∈ X.dom, ratio X L eW a w et y ≤ ratio X L eW a w et x := by
  obtain ⟨x1, hx1, he1⟩ := hne
  have h1 : 0 < ratio X L eW a w et x1 := ratio_pos hnz hx1 he1
  have hP : PnormInvStatement (E := E) := pointwiseNorm_invariance_holds
  have hinv : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      ratio X L eW a w et (lact γ (rmul x b)) = ratio X L eW a w et x := by
    intro γ hγ x hx b hb
    unfold ratio
    rw [hP r X _ _ het γ hγ x hx b hb]
    congr 2
    exact Finset.sum_congr rfl fun k _ => by rw [hP r X _ _ (hw k) γ hγ x hx b hb]
  obtain ⟨K, hK, hKd, hKs⟩ := hprop _ h1
  have hbig : ∀ y ∈ X.dom, ratio X L eW a w et x1 ≤ ratio X L eW a w et y →
      ∃ y' ∈ K, ratio X L eW a w et y' = ratio X L eW a w et y := by
    intro y hy hle
    obtain ⟨γ, hγ, b, hb, hk⟩ := hKs y hy
      ((le_div_iff₀ (pow_pos (sum_pnorm_pos hnz hy) a)).1 hle)
    exact ⟨_, hk, hinv γ hγ y hy b hb⟩
  obtain ⟨y1, hy1K, hy1⟩ := hbig x1 hx1 le_rfl
  obtain ⟨x, hxK, hxmax⟩ := hK.exists_isMaxOn ⟨y1, hy1K⟩
    ((ratio_contOn (a := a) hw hnz het).mono hKd)
  have hx1x : ratio X L eW a w et x1 ≤ ratio X L eW a w et x := hy1 ▸ isMaxOn_iff.1 hxmax y1 hy1K
  refine ⟨x, hKd hxK, fun h0 => ?_, fun y hy => ?_⟩
  · have : ratio X L eW a w et x ≤ 0 := by
      unfold ratio
      rw [pnorm_sq X _ _ (hKd hxK), h0]
      simp
    linarith
  · rcases lt_or_ge (ratio X L eW a w et y) (ratio X L eW a w et x1) with h | h
    · exact h.le.trans hx1x
    · obtain ⟨y', hy'K, hy'⟩ := hbig y hy h
      exact hy' ▸ isMaxOn_iff.1 hxmax y' hy'K

theorem log_ratio {r : ℕ} {X : Data E r} {L eW : Wt X.Ψ r} {N a : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ} {et : Frame X.Ψ r → ℂ}
    (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h : et x ≠ 0) : Real.log (ratio X L eW a w et x) =
      Real.log (Complex.normSq (et x)) + phla X (a • L - eW) x +
        (-(a : ℝ)) * Real.log (∑ k, ‖w k x‖ ^ 2) := by
  have hA : 0 < ‖et x‖ ^ 2 := pow_pos (norm_pos_iff.2 h) 2
  have hW := sum_norm_pos hnz hx
  unfold ratio
  rw [phla_lin X hx, pnorm_sq X _ _ hx, sum_pnorm_sq L w hx,
    Real.log_div (mul_pos hA (Real.exp_pos _)).ne' (pow_pos (mul_pos hW (Real.exp_pos _)) _).ne',
    Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow _ a,
    Real.log_mul hW.ne' (Real.exp_pos _).ne', Real.log_exp, Complex.normSq_eq_norm_sq]
  ring

theorem levi_pos {r : ℕ} {X : Data E r} {L eW : Wt X.Ψ r} {N a : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ} {et : Frame X.Ψ r → ℂ} (ha : 0 < a)
    (hw : ∀ k, X.IsSec L (w k)) (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) (het : X.IsSec eW et)
    (hpos : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < leviM X (phla X (a • L - eW)) x0 z ξ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (he : et x ≠ 0) (hmax : ∀ y ∈ X.dom, ratio X L eW a w et y ≤ ratio X L eW a w et x) (ξ : Fin (nd X) → ℂ)
    (hξ : ξ ≠ 0) :
    0 < (leviV (nd X) (fun z => ((Real.log (∑ k, ‖w k (cpt X x z)‖ ^ 2) : ℝ) : ℂ)) 0 ξ).re := by
  have hz : cpt X x 0 = x := IW.cpt_zero X x
  have h0 : (0 : V (nd X)) ∈ OmF X x := by
    change cpt X x 0 ∈ X.dom
    rwa [hz]
  have hO := ExF.isOpen_OmF X x
  have htn : OmF X x ∈ 𝓝 (0 : V (nd X)) := hO.mem_nhds h0
  have holo : ∀ {P : Frame X.Ψ r → ℂ}, DifferentiableOn ℂ P X.dom →
      ContDiffAt ℂ 2 (fun z => P (cpt X x z)) 0 := by
    intro P hP
    have h1 : DifferentiableOn ℂ (fun z => P (cpt X x z)) (OmF X x) :=
      hP.comp (cpt_differentiable X x).differentiableOn fun _ hz => hz
    exact ((contDiffOn_of_differentiableOn _ _ _ hO h1).contDiffAt htn).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hga := holo het.1
  have hgw : ∀ k, ContDiffAt ℂ 2 (fun z => w k (cpt X x z)) 0 := fun k =>
    holo (hw k).1
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (a : ℝ) := ⟨_, rfl⟩
  have hm' : (1 : ℝ) ≤ m := by
    rw [hm]
    exact_mod_cast ha
  obtain ⟨fα, hfα⟩ : ∃ f : V (nd X) → ℝ,
      f = fun v => Real.log (Complex.normSq (et (cpt X x v))) := ⟨_, rfl⟩
  obtain ⟨fP, hfP⟩ : ∃ f : V (nd X) → ℝ, f = fun v => phla X (a • L - eW) (cpt X x v) := ⟨_, rfl⟩
  obtain ⟨fW, hfW⟩ : ∃ f : V (nd X) → ℝ,
      f = fun v => Real.log (∑ k, ‖w k (cpt X x v)‖ ^ 2) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ f : V (nd X) → ℝ,
      f = fun v => (fα v + fP v) + (-m) * fW v := ⟨_, rfl⟩
  have hαc : ContDiffAt ℝ 2 (fun v => Complex.normSq (et (cpt X x v))) 0 := by
    have := (contDiff_norm_sq ℝ).comp_contDiffAt (0 : V (nd X)) (hga.restrict_scalars ℝ)
    simpa [Function.comp_def, Complex.normSq_eq_norm_sq] using this
  have hα0 : Complex.normSq (et (cpt X x 0)) ≠ 0 := by
    rw [hz]; exact (Complex.normSq_pos.2 he).ne'
  have hcα : ContDiffAt ℝ 2 fα 0 := by rw [hfα]; exact hαc.log hα0
  have hcP : ContDiffAt ℝ 2 fP 0 := by
    rw [hfP]; exact (IW.phla_cpt_cdAt X x h0 _).of_le (WithTop.coe_le_coe.2 le_top)
  have hWc : ContDiffAt ℝ 2 (fun v => ∑ k, ‖w k (cpt X x v)‖ ^ 2) 0 :=
    ContDiffAt.sum (fun k _ => (contDiff_norm_sq ℝ).comp_contDiffAt _ ((hgw k).restrict_scalars ℝ))
  have hW0 : (∑ k, ‖w k (cpt X x 0)‖ ^ 2) ≠ 0 := (sum_norm_pos hnz h0).ne'
  have hcW : ContDiffAt ℝ 2 fW 0 := by rw [hfW]; exact hWc.log hW0
  have hc1 : ContDiffAt ℝ 2 (fun v => fα v + fP v) 0 := hcα.add hcP
  have hc2 : ContDiffAt ℝ 2 (fun v => (-m) * fW v) 0 := contDiffAt_const.mul hcW
  have hch : ContDiffAt ℝ 2 h 0 := by rw [hh]; exact hc1.add hc2
  have hne : ∀ᶠ v in 𝓝 (0 : V (nd X)), et (cpt X x v) ≠ 0 :=
    hga.continuousAt.eventually_ne (by rw [hz]; exact he)
  have hloc : ∀ᶠ v in 𝓝 (0 : V (nd X)), h v = Real.log (ratio X L eW a w et (cpt X x v)) := by
    filter_upwards [htn, hne] with v hv hv'
    rw [log_ratio hnz hv hv', hh, hfα, hfP, hfW, hm]
  have hmaxh : IsLocalMax h 0 := by
    have h00 := hloc.self_of_nhds
    rw [hz] at h00
    filter_upwards [hloc, htn, hne] with v hv hvt hv'
    rw [hv, h00]
    exact Real.log_le_log (ratio_pos hnz hvt hv') (hmax _ hvt)
  have hL := Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax hch hmaxh ξ
  have e1 : leviV (nd X) (fun y => ((h y : ℝ) : ℂ)) 0 ξ =
      leviV (nd X) (fun y => ((fα y + fP y : ℝ) : ℂ)) 0 ξ +
        leviV (nd X) (fun y => (((-m) * fW y : ℝ) : ℂ)) 0 ξ := by
    rw [hh]; exact Y.LocalMaximumSecondDerivative.leviV_ofReal_add hc1 hc2 ξ
  have e2 : leviV (nd X) (fun y => ((fα y + fP y : ℝ) : ℂ)) 0 ξ =
      leviV (nd X) (fun y => ((fα y : ℝ) : ℂ)) 0 ξ +
        leviV (nd X) (fun y => ((fP y : ℝ) : ℂ)) 0 ξ :=
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add hcα hcP ξ
  rw [e1, e2, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ hcW] at hL
  simp only [Complex.add_re, Complex.re_ofReal_mul] at hL
  have hαnn : 0 ≤ (leviV (nd X) (fun y => ((fα y : ℝ) : ℂ)) 0 ξ).re := by
    have hpos' : 0 < ∑ _j : Fin 1, Complex.normSq (et (cpt X x 0)) := by
      simp only [Fin.sum_univ_one, hz]; exact Complex.normSq_pos.2 he
    have := leviV_log_sum_nonneg (m := 1)
      (u := fun _ v => Complex.normSq (et (cpt X x v))) (x := 0)
      (fun _ => hαc) (fun _ => logPshAt_normSq hga) hpos' ξ
    rw [hfα]; simpa using this
  have hPpos : 0 < (leviV (nd X) (fun y => ((fP y : ℝ) : ℂ)) 0 ξ).re := by
    rw [hfP]; exact hpos x hx 0 h0 ξ hξ
  have hfin : 0 < (leviV (nd X) (fun y => ((fW y : ℝ) : ℂ)) 0 ξ).re := by
    by_contra hle
    push Not at hle
    have h1 := mul_nonneg (by linarith : (0 : ℝ) ≤ m) (neg_nonneg.2 hle)
    nlinarith
  rw [hfW] at hfin
  exact hfin

end

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (L eW : Wt X.Ψ r) (N a : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (et : Frame X.Ψ r → ℂ), 0 < a → (∀ k, X.IsSec L (w k)) → (∀ x ∈ X.dom, ∃ k, w k x ≠ 0) → X.IsSec eW et → (∃ x ∈ X.dom, et x ≠ 0) → (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 → 0 < leviM X (phla X (a • L - eW)) x0 z ξ) → (∀ δ : ℝ, 0 < δ → ∃ C : Set (Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom, δ * (∑ k, X.pnorm L (w k) x ^ 2) ^ a ≤ X.pnorm eW et x ^ 2 → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C) → ∃ x ∈ X.dom, ∃ (j0 : Fin N) (jj : Fin (nd X) → Fin N), w j0 x ≠ 0 ∧ (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => w (jj k) (cpt X x z) / w j0 (cpt X x z) : V (nd X))) 0).det ≠ 0 := by
  intro E _ _ _ r X L eW N a w et ha hw hnz het hne hpos hprop
  obtain ⟨x, hx, he, hmax⟩ := exists_max hw hnz het hne hprop
  have hz : cpt X x 0 = x := IW.cpt_zero X x
  have h0 : (0 : V (nd X)) ∈ OmF X x := by
    change cpt X x 0 ∈ X.dom
    rwa [hz]
  obtain ⟨j0, jj, hj0, hdet⟩ := GlobalTheory.LeviRank.main (nd X) N (fun k z => w k (cpt X x z))
    (OmF X x) (ExF.isOpen_OmF X x) h0
    (fun k => (hw k).1.comp (cpt_differentiable X x).differentiableOn fun _ hz => hz)
    (hnz _ h0) (levi_pos ha hw hnz het hpos hx he hmax)
  exact ⟨x, hx, j0, jj, by simpa only [hz] using hj0, hdet⟩

end GlobalTheory.ProperImmersionPoint
