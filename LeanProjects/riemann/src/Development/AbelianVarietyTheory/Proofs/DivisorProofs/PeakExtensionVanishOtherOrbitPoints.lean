import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfP
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.VanishAtSStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
  Topology Filter Metric
open scoped ENNReal

noncomputable section

namespace GlobalTheory.PeakOrbit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem rank_pos (X : Data E r) (hn : 0 < nd X) : 0 < r := by
  obtain ⟨e⟩ : Nonempty (Ent X) := Fintype.card_pos_iff.1 hn
  exact Fin.pos e.2.1.1

theorem isOrth_translate (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (ho : IsOrth X x) : IsOrth X (lact γ x) := fun τ => by
  rw [OntoS.gram_lact X hγ]; exact ho τ

def testFn (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (Ψ : Frame X.Ψ r → ℝ≥0∞)
    (y : Frame X.Ψ r) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal (‖X.dom.piecewise P 0 y‖ ^ 2 * Real.exp (-(X.dom.piecewise (phla X la) 0 y))) * Ψ y

theorem testFn_dom (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (Ψ : Frame X.Ψ r → ℝ≥0∞)
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    testFn X la P Ψ y = ENNReal.ofReal (‖P y‖ ^ 2 * Real.exp (-phla X la y)) * Ψ y := by
  classical
  simp only [testFn, Set.piecewise_eq_of_mem _ _ _ hy]

theorem testFn_meas (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : ContinuousOn P X.dom)
    {Ψ : Frame X.Ψ r → ℝ≥0∞} (hΨ : Measurable Ψ) : Measurable (testFn X la P Ψ) := by
  classical
  have hm := (IW.isOpen_dom X).measurableSet
  have h1 : Measurable (X.dom.piecewise P 0) := hP.measurable_piecewise continuousOn_const hm
  have h2 : Measurable (X.dom.piecewise (phla X la) 0) :=
    (IW.phla_contOn X la).measurable_piecewise continuousOn_const hm
  unfold testFn
  exact ((h1.norm.pow_const 2).mul (h2.neg.exp)).ennreal_ofReal.mul hΨ

theorem testFn_rmul (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : IsBEq X la P)
    {Ψ : Frame X.Ψ r → ℝ≥0∞} (hΨ : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Ψ (rmul y b) = Ψ y)
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    testFn X la P Ψ (rmul y b) = testFn X la P Ψ y := by
  rw [testFn_dom X la P Ψ (OntoS.dom_rmul X hy hb), testFn_dom X la P Ψ hy,
    IW.exp_neg_phla_rmul X GlobalTheory.NormFactor.nfacRmul_holds la hy hb, hP.2 y hy b hb, hΨ y hy b hb]
  congr 2
  have : ‖bchar la b‖ ≠ 0 := norm_ne_zero_iff.2 (IW.bchar_ne_zero X hb la)
  rw [norm_mul]
  field_simp

theorem vanish_translate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), IsOrth X x → 0 < nd X →
    ∀ (Ψ : Frame X.Ψ r → ℝ≥0∞), Measurable Ψ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Ψ (rmul y b) = Ψ y) →
    (∀ γ ∈ X.Γ, ∀ y ∈ X.dom, Ψ (lact γ y) = Ψ y) → ∀ (c ρ' : ℝ), 0 < c → 0 < ρ' →
    (∀ w ∈ Metric.ball (0 : V (nd X)) ρ',
      ENNReal.ofReal (c * ‖w‖ ^ (-(2 * (nd X : ℝ)))) ≤ Ψ (cpt X x w)) →
    (∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) →
      ∀ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) →
    ∀ (F0 F : V (nd X) → ℂ), (∀ z, 1 / (100 * (r : ℝ) ^ 2) < ‖z‖ → F0 z = 0) →
    DifferentiableOn ℂ F (OmF X x) →
    ∫⁻ z, ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * Real.exp (-phla X la (cpt X x z))) * Ψ (cpt X x z)
      ∂muF X x < ⊤ →
    ∀ P : Frame X.Ψ r → ℂ, IsBEq X la P → (∀ z ∈ OmF X x, P (cpt X x z) = F z) →
    ∀ γ ∈ X.Γ, γ ≠ 1 → P (lact γ x) = 0 := by
  intro E _ _ _ r X la x ho hn Ψ hΨm hΨB hΨΓ c ρ' hc hρ' hlow hinj F0 F hF0 _ hI P hP hPF γ hγ hγ1
  by_contra hne
  have hr : (0 : ℝ) < r := Nat.cast_pos.2 (rank_pos X hn)
  have hR : (0 : ℝ) < 1 / (100 * (r : ℝ) ^ 2) := by positivity
  set x1 := lact γ x with hx1def
  have ho1 : IsOrth X x1 := isOrth_translate X hγ ho
  have h01 := IW.zero_mem_OmF X x1 ho1
  have hO1 := (ExF.isOpen_OmF X x1).mem_nhds h01
  have hO := (ExF.isOpen_OmF X x).mem_nhds (IW.zero_mem_OmF X x ho)

  set h : V (nd X) → ℝ := fun w => Real.exp (Real.log (densF X x1 w) - phla X la (cpt X x1 w)) *
    ‖P (cpt X x1 w)‖ ^ 2 with hh
  have hcont : ContinuousAt h 0 :=
    (Real.continuous_exp.continuousAt.comp (((IW.logDens_cdAt X x1 h01).sub
      (IW.phla_cpt_cdAt X x1 h01 la)).continuousAt)).mul
      (((IW.comp_cpt_diffOn X hP.1 x1).continuousOn.continuousAt hO1).norm.pow 2)
  have hh0 : 0 < h 0 := by
    simp only [hh, IW.cpt_zero]
    exact mul_pos (Real.exp_pos _) (pow_pos (norm_pos_iff.2 hne) 2)
  have hev : ∀ᶠ w in 𝓝 (0 : V (nd X)), h 0 / 2 < h w :=
    hcont.eventually (lt_mem_nhds (by linarith))
  have hall : ∀ᶠ w in 𝓝 (0 : V (nd X)), h 0 / 2 < h w ∧ w ∈ OmF X x1 ∧ w ∈ OmF X x ∧
      w ∈ ball (0 : V (nd X)) ρ' ∧ w ∈ ball (0 : V (nd X)) (1 / (100 * (r : ℝ) ^ 2)) := by
    filter_upwards [hev, hO1, hO, ball_mem_nhds 0 hρ', ball_mem_nhds 0 hR] with w a b c d e
    exact ⟨a, b, c, d, e⟩
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.1 hall
  obtain ⟨Δ, zOf, bOf, hΔd, -, hzOf, -, hdec, hlast⟩ := lu_holds (E := E) r X x1 ho1
  have hG : IsOpen {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
    hΔd.continuous.continuousOn.isOpen_inter_preimage (IW.isOpen_dom X) isOpen_compl_singleton
  have hNo : IsOpen (IW.Nset X Δ zOf ρ) := hzOf.continuousOn.isOpen_inter_preimage hG isOpen_ball
  have hN1 : ∀ w ∈ ball (0 : V (nd X)) ρ, cpt X x1 w ∈ IW.Nset X Δ zOf ρ := by
    intro w hw
    have hwO := (hsub hw).2.1
    obtain ⟨h1, h2, -⟩ := hlast w hwO (IW.idF X) (IW.idF_mem X)
    rw [IW.rmul_idF] at h1 h2
    exact ⟨⟨hwO, h1⟩, by simp only [Set.mem_preimage]; rw [h2]; exact hw⟩
  have hN2 : ∀ z, cpt X x z ∈ IW.Nset X Δ zOf ρ → z ∈ OmF X x ∧ F0 z = 0 := by
    intro z hzN
    obtain ⟨⟨hzd, hΔz⟩, hzb⟩ := hzN
    refine ⟨hzd, hF0 z (lt_of_not_ge fun hz => hγ1 ?_)⟩
    obtain ⟨-, hbO, hd⟩ := hdec _ hzd hΔz
    have e := IW.rmul_binv X (cpt X x1 (zOf (cpt X x z))) hbO
    rw [← hd, hx1def, IW.cpt_lact] at e
    have hw := (hsub hzb).2.2.2.2
    rw [mem_ball, dist_zero_right] at hw
    exact hinj γ hγ _ z hw.le hz _ (IW.binv_mem X hbO) e.symm
  have hφm : Measurable ((IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ)) :=
    (testFn_meas X la hP.1.continuousOn hΨm).indicator hNo.measurableSet
  have hφinv : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) (rmul y b) =
        (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) y := by
    intro y hy b hb
    by_cases hyN : y ∈ IW.Nset X Δ zOf ρ
    · rw [Set.indicator_of_mem hyN,
        Set.indicator_of_mem ((IW.Nset_sat X x1 hdec hlast ρ hy hb).2 hyN),
        testFn_rmul X hP hΨB hy hb]
    · rw [Set.indicator_of_notMem hyN, Set.indicator_of_notMem
        (fun h => hyN ((IW.Nset_sat X x1 hdec hlast ρ hy hb).1 h))]
  have hMI := measInv_holds (E := E) r X x x1 ho ho1 _ hφm hφinv
  have hL : ∫⁻ z, (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) (cpt X x z) ∂muF X x < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hI
    by_cases hzN : cpt X x z ∈ IW.Nset X Δ zOf ρ
    · obtain ⟨hz, hz0⟩ := hN2 z hzN
      have hzd : cpt X x z ∈ X.dom := hz
      rw [Set.indicator_of_mem hzN, testFn_dom X la P Ψ hzd, hPF z hz, hz0, zero_sub, norm_neg]
    · rw [Set.indicator_of_notMem hzN]; exact zero_le
  have hk : 0 < h 0 / 2 * c := by positivity
  have hpt : ∀ w ∈ ball (0 : V (nd X)) ρ, ENNReal.ofReal (h 0 / 2 * c) *
      ENNReal.ofReal (‖w‖ ^ (-2 * (nd X : ℝ))) ≤
      ENNReal.ofReal (densF X x1 w) * (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) (cpt X x1 w) := by
    intro w hw
    obtain ⟨h1, hw1, hw0, hwρ, -⟩ := hsub hw
    have hd := IW.densF_pos X x1 hw1
    have hwd : cpt X x1 w ∈ X.dom := hw1
    have hΨw : Ψ (cpt X x1 w) = Ψ (cpt X x w) := by
      rw [hx1def, IW.cpt_lact]; exact hΨΓ γ hγ _ hw0
    have hval : h w = densF X x1 w * (‖P (cpt X x1 w)‖ ^ 2 * Real.exp (-phla X la (cpt X x1 w))) := by
      simp only [hh]
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hd]
      ring
    rw [Set.indicator_of_mem (hN1 w hw), testFn_dom X la P Ψ hwd, hΨw, ← mul_assoc,
      ← ENNReal.ofReal_mul hd.le, ← hval, ← ENNReal.ofReal_mul hk.le, mul_assoc,
      ENNReal.ofReal_mul (by positivity), neg_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal h1.le) (hlow w hwρ)
  have hR1 : ENNReal.ofReal (h 0 / 2 * c) *
      ∫⁻ w in ball (0 : V (nd X)) ρ, ENNReal.ofReal (‖w‖ ^ (-2 * (nd X : ℝ))) ≤
      ∫⁻ w, (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) (cpt X x1 w) ∂muF X x1 := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, IW.muF_lintegral]
    exact (setLIntegral_mono' measurableSet_ball hpt).trans
      (lintegral_mono_set fun w hw => (hsub hw).2.1)
  rw [VanishPf.crit_div hn hρ, ENNReal.mul_top (ENNReal.ofReal_pos.2 hk).ne', ← hMI] at hR1
  exact absurd (hR1.trans_lt hL) (lt_irrefl _)

end GlobalTheory.PeakOrbit

end
