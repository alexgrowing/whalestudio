import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfJ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.KronSolve

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def weight (X : Data E r) (la L : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r) (bb : ℝ)
    (z : V (nd X)) : ℝ :=
  phla X la (cpt X x0 z) + ((-1) * Real.log (densF X x0 z) +
    ((-(nd X : ℝ)) * phla X L (cpt X x0 z) + (ψ (cpt X x0 z) + (-bb) * rhF X x0 z)))

theorem weight_contDiffOn (X : Data E r) (la L : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r)
    (bb : ℝ) (hψ : ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0)) :
    ContDiffOn ℝ ∞ (weight X la L ψ x0 bb) (OmF X x0) := by
  intro z hz
  have h1 := IW.phla_cpt_cdAt X x0 hz la
  have h2 := IW.logDens_cdAt X x0 hz
  have h3 := IW.phla_cpt_cdAt X x0 hz L
  have h4 := hψ.contDiffAt ((OntoB.isOpen_OmF X x0).mem_nhds hz)
  have h5 := OntoB.rhF_contDiffAt hz
  exact (h1.add ((contDiffAt_const.mul h2).add ((contDiffAt_const.mul h3).add
    (h4.add (contDiffAt_const.mul h5))))).contDiffWithinAt

theorem levi_weight (X : Data E r) (la L : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r)
    (bb : ℝ) (hψ : ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0)) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    (leviV (nd X) (fun w => ((weight X la L ψ x0 bb w : ℝ) : ℂ)) z ξ).re =
      leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ - (nd X : ℝ) * leviO X x0 (phla X L) z ξ +
        leviO X x0 ψ z ξ - bb * leviRh X x0 z ξ := by
  have h1 := (IW.phla_cpt_cdAt X x0 hz la).of_le HE.two_le_inf
  have h2 := (IW.logDens_cdAt X x0 hz).of_le HE.two_le_inf
  have h3 := (IW.phla_cpt_cdAt X x0 hz L).of_le HE.two_le_inf
  have h4 := (hψ.contDiffAt ((OntoB.isOpen_OmF X x0).mem_nhds hz)).of_le HE.two_le_inf
  have h5 : ContDiffAt ℝ 2 (fun w => rhF X x0 w) z := (OntoB.rhF_contDiffAt hz).of_le HE.two_le_inf
  unfold weight leviO leviM leviDens leviRh
  rw [Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 ((contDiffAt_const.mul h2).add ((contDiffAt_const.mul h3).add
      (h4.add (contDiffAt_const.mul h5)))),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h2) ((contDiffAt_const.mul h3).add
      (h4.add (contDiffAt_const.mul h5))),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h3) (h4.add (contDiffAt_const.mul h5)),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add h4 (contDiffAt_const.mul h5),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3,
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h5]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  ring

theorem pnorm_sq (X : Data E r) (L : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x0 : Frame X.Ψ r)
    {z : V (nd X)} (hz : z ∈ OmF X x0) :
    X.pnorm L P (cpt X x0 z) ^ 2 =
      Complex.normSq (P (cpt X x0 z)) * Real.exp (-phla X L (cpt X x0 z)) := by
  have hp := OntoE.nfac_pos X x0 (la := L) hz
  have e : X.pnorm L P (cpt X x0 z) = ‖P (cpt X x0 z)‖ * X.nfac L (cpt X x0 z) := rfl
  have e2 : Real.exp (-phla X L (cpt X x0 z)) = X.nfac L (cpt X x0 z) ^ 2 := by
    have : -phla X L (cpt X x0 z) = Real.log (X.nfac L (cpt X x0 z) ^ 2) := by
      rw [Real.log_pow]; unfold phla; push_cast; ring
    rw [this, Real.exp_log (pow_pos hp 2)]
  rw [e, e2, Complex.normSq_eq_norm_sq, mul_pow]

theorem integrand_eq (X : Data E r) (la L : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r)
    (bb : ℝ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (A : ℝ) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    densF X x0 z * (A * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z *
      (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) =
    A * Real.exp (-weight X la L ψ x0 bb z) *
      HE.nsq (fun k w => s k (cpt X x0 w)) z ^ (-(nd X : ℝ)) := by
  have hs : ∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2 =
      HE.nsq (fun k w => s k (cpt X x0 w)) z * Real.exp (-phla X L (cpt X x0 z)) := by
    unfold HE.nsq
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => pnorm_sq X L (s k) x0 hz
  rw [hs, Real.mul_rpow (HE.nsq_nonneg _ _) (Real.exp_pos _).le, ← Real.exp_mul]
  have hd : densF X x0 z = Real.exp (Real.log (densF X x0 z)) :=
    (Real.exp_log (OntoB.densF_pos hz)).symm
  have hw : Real.exp (-weight X la L ψ x0 bb z) =
      Real.exp (Real.log (densF X x0 z)) * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) *
        Real.exp (-(-bb * rhF X x0 z)) * Real.exp (-phla X L (cpt X x0 z) * -(nd X : ℝ)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold weight
    ring
  rw [hw, ← hd, kaF, Real.exp_neg (-bb * rhF X x0 z), div_eq_mul_inv]
  ring

end

end GlobalTheory.KronSolve

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kronSolve : (∀ (r : ℕ) (X : Data E r) (la L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r) (bb m η : ℝ), 0 < nd X → IsOrth X x0 → X.IsSec L w0 → (∀ k, X.IsSec L (s k)) → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0) → 0 ≤ bb → bb < m → 0 < η → (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ - (nd X : ℝ) * leviO X x0 (phla X L) z ξ + leviO X x0 ψ z ξ) → (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 2 * η * leviO X x0 (phla X L) z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ - (nd X : ℝ) * leviO X x0 (phla X L) z ξ + leviO X x0 ψ z ξ) → (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 → 0 < leviO X x0 (phla X L) z ξ) → w0 x0 ≠ 0 → (∀ k, s k x0 = 0) → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x0) z) / w0 (cpt X (x0) z) : V (nd X))) 0).det ≠ 0 → ∃ (ε : ℝ) (χ F : V (nd X) → ℂ), 0 < ε ∧ Metric.closedBall (0 : V (nd X)) (2 * ε) ⊆ OmF X x0 ∧ (∀ z ∈ Metric.closedBall (0 : V (nd X)) (2 * ε), (∀ k, s k (cpt X x0 z) = 0) → z = 0) ∧ Continuous χ ∧ (∀ z, ‖z‖ ≤ ε → χ z = 1) ∧ (∀ z, 2 * ε ≤ ‖z‖ → χ z = 0) ∧ DifferentiableOn ℂ F (OmF X x0) ∧ ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z * (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ∂muF X x0 < ⊤) := by
  intro r X la L w0 s ψ x0 bb m η hn ho hw0 hs hψ hbb hbm hη hm h2 hL hw00 hs0 hdet
  have hU := OntoB.isOpen_OmF X x0
  have h0 := IW.zero_mem_OmF X x0 ho
  have hc0 := IW.cpt_zero X x0
  have hsd : ∀ k, DifferentiableOn ℂ (fun z => s k (cpt X x0 z)) (OmF X x0) :=
    fun k => OntoB.hol_comp X x0 (hs k).1
  have hwd : DifferentiableOn ℂ (fun z => w0 (cpt X x0 z)) (OmF X x0) := OntoB.hol_comp X x0 hw0.1
  set f : V (nd X) → V (nd X) := fun z =>
    (WithLp.toLp 2 fun k => s k (cpt X x0 z) / w0 (cpt X x0 z) : V (nd X)) with hf
  have hfd : DifferentiableAt ℂ f 0 := by
    rw [differentiableAt_euclidean]
    intro k
    have hne : w0 (cpt X x0 0) ≠ 0 := by rw [hc0]; exact hw00
    have h1 := (hsd k).differentiableAt (hU.mem_nhds h0)
    have h2 := (hwd.differentiableAt (hU.mem_nhds h0)).inv hne
    have h3 := h1.mul h2
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    simp [hf, div_eq_mul_inv]
  have hf0 : f 0 = 0 := by
    ext k
    simp [hf, hc0, hs0 k]
  obtain ⟨δ, hδ, hiso⟩ := HE.iso_zero hfd.hasFDerivAt hdet hf0
  obtain ⟨k0, hk0⟩ := HE.coord_ne_of_det (f := f) hn hdet
  have hk0' : ¬ (fun z => s k0 (cpt X x0 z)) =ᶠ[𝓝 0] 0 := by
    intro h
    apply hk0
    filter_upwards [h] with z hz
    have hz' : s k0 (cpt X x0 z) = 0 := hz
    simp [hf, hz']
  have hgn := HE.hgn_of hU (OmFConnStatement_holds r X x0 ho) (hsd k0) h0 hk0'
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  set ε : ℝ := min δ ρ / 4 with hεdef
  have hmin : 0 < min δ ρ := lt_min hδ hρ
  have hε : 0 < ε := by positivity
  have hε1 : 2 * ε ≤ δ := by have := min_le_left δ ρ; linarith
  have hε2 : 2 * ε < ρ := by have := min_le_right δ ρ; linarith
  have hcb : Metric.closedBall (0 : V (nd X)) (2 * ε) ⊆ OmF X x0 :=
    (Metric.closedBall_subset_ball hε2).trans hball
  have hiso' : ∀ z ∈ Metric.closedBall (0 : V (nd X)) (2 * ε),
      (∀ k, s k (cpt X x0 z) = 0) → z = 0 := by
    intro z hz hsz
    refine hiso z (Metric.closedBall_subset_closedBall hε1 hz) ?_
    ext k
    simp [hf, hsz k]
  have hW := KronSolve.weight_contDiffOn X la L ψ x0 bb hψ
  have hWpos : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < (leviV (nd X) (fun w => ((KronSolve.weight X la L ψ x0 bb w : ℝ) : ℂ)) z ξ).re := by
    intro z hz ξ hξ
    rw [KronSolve.levi_weight X la L ψ x0 bb hψ hz ξ]
    have a1 := hm z hz ξ
    have a2 := h2 z hz ξ
    have a3 := hL z hz ξ hξ
    set Q := leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ -
      (nd X : ℝ) * leviO X x0 (phla X L) z ξ + leviO X x0 ψ z ξ
    set R := leviRh X x0 z ξ
    have hQ : 0 < Q := lt_of_lt_of_le (by positivity) a2
    have hm0 : 0 < m := lt_of_le_of_lt hbb hbm
    have : 0 < m * (Q - bb * R) := by
      have b1 : 0 < (m - bb) * Q := mul_pos (by linarith) hQ
      have b2 : 0 ≤ bb * (Q - m * R) := mul_nonneg hbb (by linarith)
      nlinarith
    exact (mul_pos_iff_of_pos_left hm0).1 this
  have hWnn : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ (leviV (nd X) (fun w => ((KronSolve.weight X la L ψ x0 bb w : ℝ) : ℂ)) z ξ).re := by
    intro z hz ξ
    by_cases hξ : ξ = 0
    · subst hξ
      simp [leviV]
    · exact (hWpos z hz ξ hξ).le
  obtain ⟨c, hc, hunif⟩ := HE.levi_unif hU hW (isCompact_closedBall (0 : V (nd X)) (2 * ε)) hcb
    (fun z hz => hWpos z (hcb hz))
  have he : ContDiffOn ℝ ∞ (eF X x0) (OmF X x0) :=
    fun z hz => (ExF.eF_contDiffAt X x0 ho hz).contDiffWithinAt
  have hel : ∀ y ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ (leviV (nd X) (fun w => ((eF X x0 w : ℝ) : ℂ)) y ξ).re := by
    intro y hy ξ
    have e1 : (fun y : V (nd X) => ((eF X x0 y : ℝ) : ℂ)) =
        fun y => ((rhF X x0 y + Real.log (1 + ‖y‖ ^ 2) : ℝ) : ℂ) := rfl
    rw [e1, Y.LocalMaximumSecondDerivative.leviV_ofReal_add
      ((ExF.rhF_contDiffAt X x0 ho hy).of_le HE.two_le_inf)
      (ExF.T_cd.contDiffAt.of_le HE.two_le_inf) ξ, Complex.add_re]
    exact add_nonneg (ExF.levi_rhF_nonneg X x0 ho hy ξ) (ExF.leviT_nonneg _ ξ)
  have he0 : ∀ y ∈ OmF X x0, 0 ≤ eF X x0 y := fun y hy =>
    add_nonneg (ExF.rhF_nonneg X x0 ho hy) (Real.log_nonneg (by nlinarith [sq_nonneg ‖y‖]))
  obtain ⟨F, hFd, hF⟩ := HE.interp_euclid hU (eF X x0) he hel (ExF.isCompact_subF X x0 ho) he0
    (fun k w => s k (cpt X x0 w)) hsd k0 hgn (KronSolve.weight X la L ψ x0 bb) hW hWnn ε hε hcb hiso'
    c hc hunif
  refine ⟨ε, HE.cut ε hε, F, hε, hcb, hiso', (HE.cut_contDiff ε hε).continuous,
    fun z hz => HE.cut_one ε hε hz, fun z hz => HE.cut_zero ε hε hz, hFd, ?_⟩
  refine lt_of_eq_of_lt ?_ hF
  unfold muF
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (OntoC.measurable_densF X x0)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setLIntegral_congr_fun hU.measurableSet fun z hz => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (OntoB.densF_pos hz).le, KronSolve.integrand_eq X la L ψ x0 bb s _ hz]

end GlobalTheory
