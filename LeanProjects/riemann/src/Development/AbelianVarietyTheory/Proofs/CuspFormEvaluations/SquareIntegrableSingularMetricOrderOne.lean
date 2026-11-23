import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurablePhi
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormLeOfDet
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuUnconditional
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FreeWeightInFF

open Filter GlobalTheory.Up GlobalTheory.Up.DivInFFPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r)

open Classical in

noncomputable def Wfree (n : ℕ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) *
    ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
    ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0

theorem Wfree_of_mem (n : ℕ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Wfree Xa Fl G n x = ENNReal.ofReal (Real.exp (-phla X G x)) *
      ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
      ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
  unfold Wfree
  rw [if_pos hx]

theorem Wfree_eq_pnorm (n : ℕ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Wfree Xa Fl G n x = ENNReal.ofReal (Real.exp (-phla X (G + n • Xa.L) x)) *
      ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(1 / 2 : ℝ)) *
      ENNReal.ofReal (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
  have hw : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Xa.w k x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx Xa.L (Xa.w k)
  have hs : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Fl.s k x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx Xa.L (Fl.s k)
  have he : Real.exp (-phla X (G + n • Xa.L) x) =
      Real.exp (-phla X G x) * Real.exp (-phla X Xa.L x) ^ n := by
    rw [GlobalTheory.Up.phla_add_nsmul hx, neg_add, Real.exp_add, ← Real.exp_nat_mul, mul_neg]
  have hc0 : ENNReal.ofReal (Real.exp (-phla X Xa.L x)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have key : ENNReal.ofReal (Real.exp (-phla X Xa.L x)) ^ n *
      (ENNReal.ofReal (Real.exp (-phla X Xa.L x)) ^ (-(1 / 2 : ℝ)) *
        ENNReal.ofReal (Real.exp (-phla X Xa.L x)) ^ (-((n : ℝ) - 1 / 2))) = 1 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_add _ _ hc0 ENNReal.ofReal_ne_top,
      ← ENNReal.rpow_add _ _ hc0 ENNReal.ofReal_ne_top]
    convert ENNReal.rpow_zero using 2
    ring
  rw [Wfree_of_mem Xa Fl G n hx, hw, hs, he, ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_pow (Real.exp_pos _).le,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  generalize ENNReal.ofReal (Real.exp (-phla X Xa.L x)) = c at key ⊢
  generalize ENNReal.ofReal (Real.exp (-phla X G x)) = a
  generalize ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) = A
  generalize ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) = B
  calc a * A ^ (-(1 / 2 : ℝ)) * B ^ (-((n : ℝ) - 1 / 2))
      = a * A ^ (-(1 / 2 : ℝ)) * B ^ (-((n : ℝ) - 1 / 2)) *
        (c ^ n * (c ^ (-(1 / 2 : ℝ)) * c ^ (-((n : ℝ) - 1 / 2)))) := by rw [key, mul_one]
    _ = _ := by ring

noncomputable def phiW (n : ℕ) (h : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  ENNReal.ofReal (X.dom.indicator (fun x => X.pnorm (G + n • Xa.L) h x ^ 2) x *
    X.dom.indicator (fun x => ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) x ^ (-(1 / 2 : ℝ)) *
    X.dom.indicator (fun x => ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) x ^ (-((n : ℝ) - 1 / 2)))

theorem phiW_of_mem (n : ℕ) (h : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phiW Xa Fl G n h x = ENNReal.ofReal (X.pnorm (G + n • Xa.L) h x ^ 2 *
      (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(1 / 2 : ℝ)) *
      (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ (-((n : ℝ) - 1 / 2))) := by
  simp only [phiW, Set.indicator_of_mem hx]

theorem measurable_phiW (n : ℕ) {h : Frame X.Ψ r → ℂ} (hh : X.IsSec (G + n • Xa.L) h) :
    Measurable (phiW Xa Fl G n h) := by
  have h1 : Measurable (X.dom.indicator fun x => X.pnorm (G + n • Xa.L) h x ^ 2) :=
    GlobalTheory.Up.DivInFFPf.measurable_cut ((GlobalTheory.Up.DivInFFPf.pnorm_contOn hh).pow 2)
  have h2 : Measurable (X.dom.indicator fun x => ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) :=
    GlobalTheory.Up.DivInFFPf.measurable_cut (continuousOn_finsetSum _ fun k _ =>
      (GlobalTheory.Up.DivInFFPf.pnorm_contOn (Xa.w_van k).1.1.1).pow 2)
  have h3 : Measurable (X.dom.indicator fun x => ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) :=
    GlobalTheory.Up.DivInFFPf.measurable_cut (continuousOn_finsetSum _ fun k _ =>
      (GlobalTheory.Up.DivInFFPf.pnorm_contOn (Fl.s_van k).1.1.1).pow 2)
  exact ((h1.mul (h2.pow_const _)).mul (h3.pow_const _)).ennreal_ofReal

theorem phiW_inv (hN : NfacRmulStatement (E := E)) (hN' : NfacLactStatement (E := E)) (n : ℕ)
    {h : Frame X.Ψ r → ℂ} (hh : X.IsSec (G + n • Xa.L) h) :
    ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, phiW Xa Fl G n h (lact γ (rmul x b)) = phiW Xa Fl G n h x := by
  intro γ hγ x hx b hb
  have hxb : rmul x b ∈ X.dom := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul (X := X) hx hb
  have hy : lact γ (rmul x b) ∈ X.dom :=
    (ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lact_mem_dom_iff (X := X) hγ (rmul x b)).2 hxb
  have inv : ∀ {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}, X.IsSec la P →
      X.pnorm la P (lact γ (rmul x b)) = X.pnorm la P x := fun hP =>
    (GlobalTheory.Up.DivMetricPf.pnorm_lact hN' hP hγ hxb).trans (GlobalTheory.Up.DivMetricPf.pnorm_rmul hN hP hx hb)
  have hw : ∑ k, X.pnorm Xa.L (Xa.w k) (lact γ (rmul x b)) ^ 2 = ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 :=
    Finset.sum_congr rfl fun k _ => by rw [inv (Xa.w_van k).1.1.1]
  have hs : ∑ k, X.pnorm Xa.L (Fl.s k) (lact γ (rmul x b)) ^ 2 = ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 :=
    Finset.sum_congr rfl fun k _ => by rw [inv (Fl.s_van k).1.1.1]
  rw [phiW_of_mem Xa Fl G n h hy, phiW_of_mem Xa Fl G n h hx, inv hh, hw, hs]

theorem phiW_eq (n : ℕ) (h : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hs : ∃ k, Fl.s k x ≠ 0) :
    phiW Xa Fl G n h x = ENNReal.ofReal (‖h x‖ ^ 2) * Wfree Xa Fl G n x := by
  have hw := GlobalTheory.Up.DivInFFPf.sum_pnorm_pos (la := Xa.L) hx (Xa.w_nz x hx)
  have hs' := GlobalTheory.Up.DivInFFPf.sum_pnorm_pos (la := Xa.L) hx hs
  rw [phiW_of_mem Xa Fl G n h hx, Wfree_eq_pnorm Xa Fl G n hx,
    GlobalTheory.Up.pnorm_sq_eq_exp hx (G + n • Xa.L) h, ENNReal.ofReal_rpow_of_pos hw,
    ENNReal.ofReal_rpow_of_pos hs', ENNReal.ofReal_mul, ENNReal.ofReal_mul, ENNReal.ofReal_mul]
  · ring
  all_goals positivity

theorem phiW_le_local {n : ℕ} (hn : 1 ≤ n) (h : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phiW Xa Fl G n h x ≤
      ENNReal.ofReal (X.nfac G x ^ 2 * (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (‖h x‖ ^ 2 * (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2))) := by
  refine le_of_eq ?_
  have hw : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Xa.w k x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx Xa.L (Xa.w k)
  have hs : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Fl.s k x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx Xa.L (Fl.s k)
  have he : Real.exp (-phla X (G + n • Xa.L) x) =
      Real.exp (-phla X G x) * Real.exp (-phla X Xa.L x) ^ n := by
    rw [GlobalTheory.Up.phla_add_nsmul hx, neg_add, Real.exp_add, ← Real.exp_nat_mul, mul_neg]
  have hL := Real.exp_pos (-phla X Xa.L x)
  have hA : 0 ≤ ∑ k, ‖Xa.w k x‖ ^ 2 := by positivity
  have hB : 0 ≤ ∑ k, ‖Fl.s k x‖ ^ 2 := by positivity
  have key : Real.exp (-phla X Xa.L x) ^ n * (Real.exp (-phla X Xa.L x) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-phla X Xa.L x) ^ (-((n : ℝ) - 1 / 2))) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL, ← Real.rpow_add hL]
    convert Real.rpow_zero _ using 2
    ring
  have hp : 0 ≤ Real.exp (-phla X G x) * (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) := by positivity
  rw [phiW_of_mem Xa Fl G n h hx, GlobalTheory.Up.pnorm_sq_eq_exp hx (G + n • Xa.L) h, hw, hs, he,
    Real.mul_rpow hL.le hA, Real.mul_rpow hL.le hB, ← GlobalTheory.Up.DivMetricPf.exp_neg_phla hx G,
    ← ENNReal.ofReal_mul hp]
  congr 1
  generalize Real.exp (-phla X Xa.L x) = c at key ⊢
  linear_combination (Real.exp (-phla X G x) * (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ‖h x‖ ^ 2 *
    (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2))) * key

theorem localW_int {n : ℕ} (hn : 1 ≤ n) (h : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r} (hy : y ∈ X.dom)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hint : ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (‖h (cpt X y z)‖ ^ 2 *
      (∑ k, ‖Fl.s k (cpt X y z)‖ ^ 2) ^ (-((n : ℝ) - 1 / 2))) < ⊤) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ∫⁻ z in Metric.ball (0 : V (nd X)) ρ', phiW Xa Fl G n h (cpt X y z) < ⊤ := by
  have hO : IsOpen (OmF X y) := ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.isOpen_OmF X y
  have h0 : (0 : V (nd X)) ∈ OmF X y := by
    show cpt X y 0 ∈ X.dom
    rw [ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero X y]
    exact hy
  have hwc : ContinuousOn (fun z => ∑ k, ‖Xa.w k (cpt X y z)‖ ^ 2) (OmF X y) :=
    continuousOn_finsetSum _ fun k _ =>
      ((((Xa.w_van k).1.1.1.1.continuousOn).comp
        (ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.cpt_cont X y).continuousOn fun z hz => hz).norm).pow 2
  have hpos0 : 0 < ∑ k, ‖Xa.w k (cpt X y 0)‖ ^ 2 := GlobalTheory.Up.sum_normSq_w_pos Xa (x := cpt X y 0) h0
  have hFc : ContinuousAt (fun z => X.nfac G (cpt X y z) ^ 2 *
      (∑ k, ‖Xa.w k (cpt X y z)‖ ^ 2) ^ (-(1 / 2 : ℝ))) 0 :=
    (((ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_cont (X := X) (x0 := y) G).continuousAt
      (hO.mem_nhds h0)).pow 2).mul ((hwc.continuousAt (hO.mem_nhds h0)).rpow_const (Or.inl hpos0.ne'))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((hFc.eventually (gt_mem_nhds (lt_add_one _))).and (hO.mem_nhds h0))
  refine ⟨min ρ ε, lt_min hρ hε, ?_⟩
  calc ∫⁻ z in Metric.ball (0 : V (nd X)) (min ρ ε), phiW Xa Fl G n h (cpt X y z)
      ≤ ∫⁻ z in Metric.ball (0 : V (nd X)) (min ρ ε),
          ENNReal.ofReal (X.nfac G (cpt X y 0) ^ 2 * (∑ k, ‖Xa.w k (cpt X y 0)‖ ^ 2) ^ (-(1 / 2 : ℝ)) + 1) *
          ENNReal.ofReal (‖h (cpt X y z)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X y z)‖ ^ 2) ^ (-((n : ℝ) - 1 / 2))) := by
        refine setLIntegral_mono' Metric.isOpen_ball.measurableSet fun z hz => ?_
        have hz' := hball z (Metric.ball_subset_ball (min_le_right ρ ε) hz)
        exact (phiW_le_local Xa Fl G hn h (x := cpt X y z) hz'.2).trans
          (mul_le_mul' (ENNReal.ofReal_le_ofReal hz'.1.le) le_rfl)
    _ = ENNReal.ofReal (X.nfac G (cpt X y 0) ^ 2 * (∑ k, ‖Xa.w k (cpt X y 0)‖ ^ 2) ^ (-(1 / 2 : ℝ)) + 1) *
          ∫⁻ z in Metric.ball (0 : V (nd X)) (min ρ ε),
            ENNReal.ofReal (‖h (cpt X y z)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X y z)‖ ^ 2) ^ (-((n : ℝ) - 1 / 2))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((lintegral_mono_set (Metric.ball_subset_ball (min_le_left ρ ε))).trans_lt hint)

theorem inFF_sub {T : ℕ} (hT1 : 1 ≤ T) (hnT : nd X ≤ T) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) {f g : Frame X.Ψ r → ℂ}
    (hf : X.IsSec (G + T • Xa.L) f) (hg : X.IsSec (G + T • Xa.L) g)
    (hfi : ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (G + T • Xa.L) f (cpt X x0 z) ^ 2 *
      (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(T : ℝ))) ∂muF X x0 < ⊤)
    {C : ℝ} (hC : ∀ x ∈ X.dom,
      X.pnorm (G + T • Xa.L) g x ^ 2 ≤ C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ T)
    (hvan : VanS X Fl.xs Fl.s (T - nd X) (fun x => f x - g x)) :
    InFF X x0 (Wfree Xa Fl G T) FF (fun x => f x - g x) := by
  have hM := GlobalTheory.FrameMeasureClosed.measInv_holds (E := E)
  have hN := GlobalTheory.NormFactor.nfacRmul_holds (E := E)
  have hN' := GlobalTheory.NormFactor.nfacLact_holds (E := E)
  have hfin := GlobalTheory.DriftCovolume.finMu_unconditional r X
  have hd : X.IsSec (G + T • Xa.L) (fun x => f x - g x) := by
    refine ⟨hf.1.sub hg.1, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
    · simp only [hf.2.1 x hx b hb, hg.2.1 x hx b hb]; ring
    · simp only [hf.2.2 γ hγ x hx, hg.2.2 γ hγ x hx]; ring
  have hφm := measurable_phiW Xa Fl G T hd
  have hφi := phiW_inv Xa Fl G hN hN' T hd
  have hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      phiW Xa Fl G T (fun x => f x - g x) (rmul x b) = phiW Xa Fl G T (fun x => f x - g x) x := by
    intro x hx b hb
    have := hφi 1 X.Γ.one_mem x hx b hb
    rwa [ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lact_one] at this

  have hloc : ∀ j, ∃ x1 : Frame X.Ψ r, ∃ ρ1 : ℝ, IsOrth X x1 ∧ 0 < ρ1 ∧
      Metric.ball (0 : V (nd X)) ρ1 ⊆ OmF X x1 ∧ (∃ b ∈ Bor X.Ψ r, Fl.xs j = rmul x1 b) ∧
      ∫⁻ y in Metric.ball (0 : V (nd X)) ρ1, phiW Xa Fl G T (fun x => f x - g x) (cpt X x1 y) ∂muF X x1 < ⊤ := by
    intro j
    obtain ⟨ρ, hρ, hint⟩ := hvan j
    have hexp : (-(((T - nd X : ℕ) : ℝ) + (nd X : ℝ) - 1 / 2)) = -((T : ℝ) - 1 / 2) := by
      rw [Nat.cast_sub hnT]; ring
    rw [hexp] at hint
    obtain ⟨ρ', hρ', hint'⟩ := localW_int Xa Fl G hT1 (fun x => f x - g x) (Fl.xs_mem j) hρ hint
    obtain ⟨x1, ho1, b, hb, hxs⟩ := ReciprocityTheory.ChartRestriction.G.AR.Up.ortho_holds r X (Fl.xs j) (Fl.xs_mem j)
    rw [hxs] at hint'
    obtain ⟨ρ1, hρ1, hsub, hfin1⟩ :=
      GlobalTheory.ChartChange.chart_change r X x1 b ho1 hb _ hφm hφB ρ' hρ' hint'
    exact ⟨x1, ρ1, ho1, hρ1, hsub, ⟨b, hb, hxs⟩, hfin1⟩
  choose x1 ρ1 ho1 hρ1 hsub hxb hfin1 using hloc
  obtain ⟨U, hU⟩ : ∃ U : Set (Frame X.Ψ r), U = ⋃ j, {x | ∃ y ∈ Metric.ball (0 : V (nd X)) (ρ1 j),
      ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X (x1 j) y) b)} := ⟨_, rfl⟩
  have hUo : IsOpen U := by
    rw [hU]
    exact isOpen_iUnion fun j =>
      GlobalTheory.SatOpen.isOpen_saturation r X (x1 j) (ho1 j) _ Metric.isOpen_ball (hsub j)
  have hxsU : ∀ j, Fl.xs j ∈ U := by
    intro j
    obtain ⟨b, hb, hxs⟩ := hxb j
    rw [hU, Set.mem_iUnion]
    refine ⟨j, 0, Metric.mem_ball_self (hρ1 j), 1, X.Γ.one_mem, b, hb, ?_⟩
    rw [ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lact_one, ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero]
    exact hxs
  have hsat : ∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U := by
    intro x hx γ hγ b hb
    rw [hU, Set.mem_iUnion] at hx ⊢
    obtain ⟨j, y, hy, γ0, hγ0, b0, hb0, rfl⟩ := hx
    refine ⟨j, y, hy, γ * γ0, X.Γ.mul_mem hγ hγ0, ReciprocityTheory.ChartRestriction.G.AR.Up.IW.bmul X b0 b,
      ReciprocityTheory.ChartRestriction.G.AR.Up.IW.bmul_mem (X := X) hb0 hb, ?_⟩
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.IW.lact_rmul, ReciprocityTheory.ChartRestriction.G.AR.Up.IW.lact_lact,
      ReciprocityTheory.ChartRestriction.G.AR.Up.IW.rmul_rmul]
  obtain ⟨K, hK⟩ := Fl.family_le_coords U hUo hxsU hsat
  have hAo : IsOpen (cpt X x0 ⁻¹' U) := hUo.preimage (ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.cpt_cont X x0)

  have hae : (fun z => ENNReal.ofReal (‖f (cpt X x0 z) - g (cpt X x0 z)‖ ^ 2) * Wfree Xa Fl G T (cpt X x0 z))
      =ᵐ[(muF X x0).restrict FF] fun z => phiW Xa Fl G T (fun x => f x - g x) (cpt X x0 z) := by
    filter_upwards [ae_restrict_of_ae (GlobalTheory.Up.DivInFFPf.ae_exists_ne Xa Fl ho), ae_restrict_mem hF.1]
      with z hz hzF
    exact (phiW_eq Xa Fl G T (fun x => f x - g x) (x := cpt X x0 z) (hF.2.1 hzF) (hz (hF.2.1 hzF))).symm

  have h1 : ∫⁻ z in FF ∩ cpt X x0 ⁻¹' U, phiW Xa Fl G T (fun x => f x - g x) (cpt X x0 z) ∂muF X x0 < ⊤ := by
    have hsubU : FF ∩ cpt X x0 ⁻¹' U ⊆ ⋃ j, FF ∩ {z | ∃ y ∈ Metric.ball (0 : V (nd X)) (ρ1 j),
        ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (cpt X (x1 j) y) b)} := by
      intro z hz
      have hzU := hz.2
      rw [Set.mem_preimage, hU, Set.mem_iUnion] at hzU
      obtain ⟨j, hj⟩ := hzU
      exact Set.mem_iUnion.2 ⟨j, hz.1, hj⟩
    calc _ ≤ _ := lintegral_mono_set hsubU
      _ ≤ ∑' j, ∫⁻ z in FF ∩ {z | ∃ y ∈ Metric.ball (0 : V (nd X)) (ρ1 j),
          ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (cpt X (x1 j) y) b)},
            phiW Xa Fl G T (fun x => f x - g x) (cpt X x0 z) ∂muF X x0 := lintegral_iUnion_le _ _
      _ ≤ ∑' j, ∫⁻ y in Metric.ball (0 : V (nd X)) (ρ1 j),
            phiW Xa Fl G T (fun x => f x - g x) (cpt X (x1 j) y) ∂muF X (x1 j) :=
        ENNReal.tsum_le_tsum fun j => GlobalTheory.Unfold.lintegral_fundSet_inter_le hM r X x0 (x1 j) ho (ho1 j)
          FF hF _ hφm hφi _ Metric.isOpen_ball.measurableSet (hsub j)
      _ < ⊤ := by
        rw [tsum_fintype]
        exact ENNReal.sum_lt_top.2 fun j _ => hfin1 j

  have hc0 : (0 : ℝ) ≤ 2 * |K| ^ ((T : ℝ) - 1 / 2) := by positivity
  have hpt : ∀ z ∈ FF \ cpt X x0 ⁻¹' U, phiW Xa Fl G T (fun x => f x - g x) (cpt X x0 z) ≤
      ENNReal.ofReal (2 * |K| ^ ((T : ℝ) - 1 / 2)) *
        ENNReal.ofReal (X.pnorm (G + T • Xa.L) f (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(T : ℝ))) +
      ENNReal.ofReal (2 * |K| ^ ((T : ℝ) - 1 / 2) * C) := by
    intro z hz
    have hx : cpt X x0 z ∈ X.dom := hF.2.1 hz.1
    have hxU : cpt X x0 z ∉ U := hz.2
    have hw0 := GlobalTheory.Up.DivInFFPf.sum_pnorm_pos (la := Xa.L) hx (Xa.w_nz _ hx)
    have hs0 : 0 ≤ ∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x0 z) ^ 2 := by positivity
    have key := GlobalTheory.Up.DivInFFPf.real_bound (a := f (cpt X x0 z)) (b := g (cpt X x0 z)) hT1
      (Real.exp_pos (-phla X (G + T • Xa.L) (cpt X x0 z))).le
      (GlobalTheory.Up.pnorm_sq_eq_exp hx _ f) (GlobalTheory.Up.pnorm_sq_eq_exp hx _ g) hw0 hs0 (hK _ hx hxU) (hC _ hx)
    rw [phiW_of_mem Xa Fl G T _ hx, GlobalTheory.Up.pnorm_sq_eq_exp hx (G + T • Xa.L) (fun x => f x - g x),
      ← ENNReal.ofReal_mul hc0]
    exact (ENNReal.ofReal_le_ofReal key).trans ENNReal.ofReal_add_le
  have h2 : ∫⁻ z in FF \ cpt X x0 ⁻¹' U, phiW Xa Fl G T (fun x => f x - g x) (cpt X x0 z) ∂muF X x0 < ⊤ := by
    calc _ ≤ ∫⁻ z in FF \ cpt X x0 ⁻¹' U, (ENNReal.ofReal (2 * |K| ^ ((T : ℝ) - 1 / 2)) *
          ENNReal.ofReal (X.pnorm (G + T • Xa.L) f (cpt X x0 z) ^ 2 *
            (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(T : ℝ))) +
          ENNReal.ofReal (2 * |K| ^ ((T : ℝ) - 1 / 2) * C)) ∂muF X x0 :=
        setLIntegral_mono' (hF.1.diff hAo.measurableSet) hpt
      _ ≤ ∫⁻ z in FF, (ENNReal.ofReal (2 * |K| ^ ((T : ℝ) - 1 / 2)) *
          ENNReal.ofReal (X.pnorm (G + T • Xa.L) f (cpt X x0 z) ^ 2 *
            (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(T : ℝ))) +
          ENNReal.ofReal (2 * |K| ^ ((T : ℝ) - 1 / 2) * C)) ∂muF X x0 :=
        lintegral_mono_set fun z hz => hz.1
      _ = ENNReal.ofReal (2 * |K| ^ ((T : ℝ) - 1 / 2)) *
          ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (G + T • Xa.L) f (cpt X x0 z) ^ 2 *
            (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(T : ℝ))) ∂muF X x0 +
          ENNReal.ofReal (2 * |K| ^ ((T : ℝ) - 1 / 2) * C) * muF X x0 FF := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          setLIntegral_const]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfi,
          ENNReal.mul_lt_top ENNReal.ofReal_lt_top (GlobalTheory.Up.DivInFFPf.muF_lt_top hM hfin ho hF)⟩
  show ∫⁻ z in FF, ENNReal.ofReal (‖f (cpt X x0 z) - g (cpt X x0 z)‖ ^ 2) * Wfree Xa Fl G T (cpt X x0 z)
    ∂muF X x0 < ⊤
  rw [lintegral_congr_ae hae]
  calc _ = ∫⁻ z in FF ∩ cpt X x0 ⁻¹' U ∪ FF \ cpt X x0 ⁻¹' U,
        phiW Xa Fl G T (fun x => f x - g x) (cpt X x0 z) ∂muF X x0 := by rw [Set.inter_union_sdiff]
    _ ≤ _ := lintegral_union_le _ _ _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨h1, h2⟩

theorem inFF_order_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ f : Frame X.Ψ r → ℂ, X.IsSec (G + (nd X + 1) • Xa.L) f → (∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (G + (nd X + 1) • Xa.L) f x ^ 2 ≤ C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (nd X + 1)) → (∀ j, f (Fl.xs j) = 0) → InFF X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X + 1 : ℕ) : ℝ) - 1 / 2)) else 0) FF f := by
  intro E _ _ _ r X Xa Fl G x0 ho FF hF f hf hbd hzero
  obtain ⟨C, hC⟩ := hbd
  have hM := GlobalTheory.FrameMeasureClosed.measInv_holds (E := E)
  have hfin := GlobalTheory.DriftCovolume.finMu_unconditional r X
  have hfi : ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (G + (nd X + 1) • Xa.L) f (cpt X x0 z) ^ 2 *
      (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-((nd X + 1 : ℕ) : ℝ))) ∂muF X x0 < ⊤ := by
    calc _ ≤ ∫⁻ _ in FF, ENNReal.ofReal C ∂muF X x0 := by
          refine setLIntegral_mono' hF.1 fun z hz => ENNReal.ofReal_le_ofReal ?_
          have hx : cpt X x0 z ∈ X.dom := hF.2.1 hz
          have hS := GlobalTheory.Up.DivInFFPf.sum_pnorm_pos (la := Xa.L) hx (Xa.w_nz _ hx)
          calc _ ≤ C * (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (nd X + 1) *
                (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-((nd X + 1 : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_right (hC _ hx) (Real.rpow_nonneg hS.le _)
            _ = C := by
              rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hS]
              simp
      _ = ENNReal.ofReal C * muF X x0 FF := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (GlobalTheory.Up.DivInFFPf.muF_lt_top hM hfin ho hF)
  have hzsec : X.IsSec (G + (nd X + 1) • Xa.L) (fun _ => (0 : ℂ)) :=
    ⟨differentiableOn_const 0, fun x _ b _ => by simp, fun γ _ x _ => by simp⟩
  have hg0 : ∀ x ∈ X.dom, X.pnorm (G + (nd X + 1) • Xa.L) (fun _ => (0 : ℂ)) x ^ 2 ≤
      0 * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (nd X + 1) := fun x _ => by
    simp [ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm]
  have hvan : VanS X Fl.xs Fl.s (nd X + 1 - nd X) (fun x => f x - (fun _ => (0 : ℂ)) x) := by
    rw [show nd X + 1 - nd X = 1 by omega]
    refine GlobalTheory.vanS_of_isBigO r X Xa Fl 1 _ (hf.1.continuousOn.sub continuousOn_const) fun j => ?_
    have hyd : cpt X (Fl.xs j) 0 ∈ X.dom := by
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero]
      exact Fl.xs_mem j
    have hd : DifferentiableAt ℂ (fun z => f (cpt X (Fl.xs j) z)) 0 :=
      (hf.1.differentiableAt ((ReciprocityTheory.ChartRestriction.G.AR.Up.IW.isOpen_dom X).mem_nhds hyd)).comp 0
        ((ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_diff X (Fl.xs j)) 0)
    have h0 : f (cpt X (Fl.xs j) 0) = 0 := by
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero]
      exact hzero j
    have hb := hd.isBigO_sub.norm_right
    simp only [h0, sub_zero] at hb
    simpa only [sub_zero, pow_one] using hb
  have key := inFF_sub Xa Fl G (T := nd X + 1) (Nat.le_add_left 1 (nd X)) (Nat.le_succ (nd X)) ho hF
    hf hzsec hfi (C := 0) hg0 hvan
  simp only [sub_zero] at key
  exact key

end GlobalTheory.FreeWeightInFF
