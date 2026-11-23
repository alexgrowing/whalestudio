import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustGPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Complex Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates UpDivD
open scoped ENNReal ContDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace UpDivG

variable {r : ℕ}

theorem sum_bdd (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (P : Fin N → Frame X.Ψ r → ℂ)
    (hP : ∀ k, X.IsBddSec la (P k)) : ∃ C : ℝ, ∀ x ∈ X.dom, ∑ k, X.pnorm la (P k) x ^ 2 ≤ C := by
  choose C hC using fun k => (hP k).2
  refine ⟨∑ k, C k ^ 2, fun x hx => Finset.sum_le_sum fun k _ => ?_⟩
  have h0 : 0 ≤ X.pnorm la (P k) x := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun τ _ =>
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  exact pow_le_pow_left₀ h0 (hC k x hx) 2

end UpDivG

theorem upDiv_holds : UpDivStatement (E := E) := by
  intro r X Xa Fl _ _ bb m _ hm hmar _ x0 ho F hF hIn
  classical
  have hU : IsOpen (OmF X x0) := OntoB.isOpen_OmF X x0
  have hUc : IsPreconnected (OmF X x0) := OFC.omFConn_of_cm r X x0 ho
  have hbm : bb ≤ m := by
    have : 0 ≤ bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) := by positivity
    linarith
  have hn2 : 2 ≤ nd X := Xa.n_ge
  have hTn : nd X ≤ Xa.T := by have := Xa.T_ge; nlinarith
  have hInU := hIn
  unfold InAt at hInU
  rw [IW.muF_lintegral] at hInU
  obtain ⟨Cs, hCs⟩ := UpDivG.sum_bdd X Xa.L Fl.s (fun k => (Fl.s_van k).1.1)
  obtain ⟨Cw, hCw⟩ := UpDivG.sum_bdd X Xa.L Xa.w (fun k => (Xa.w_van k).1.1)
  by_cases hex : ∃ k, ∃ z ∈ OmF X x0, Fl.s k (cpt X x0 z) ≠ 0
  swap
  ·
    simp only [not_exists, not_and, not_not] at hex
    have hWtop : ∀ z ∈ OmF X x0, WSk X Xa Fl (cpt X x0 z) = ⊤ := by
      intro z hz
      have hp : cpt X x0 z ∈ X.dom := hz
      have hs0 : ∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x0 z) ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [pnorm_sq X hp, hex k z hz, norm_zero]; ring
      have hwp : 0 < ∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2 := by
        rw [sumL_eq X Xa x0 hz]; exact mul_pos (Real.exp_pos _) (Sw_pos X Xa x0 hz)
      unfold WSk
      rw [if_pos hp, hs0, zero_div, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by
        have : (1 : ℝ) ≤ Xa.T := by exact_mod_cast (show 1 ≤ Xa.T by omega)
        linarith)]
      refine ENNReal.mul_top ?_
      exact mul_ne_zero (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
        (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hwp) ENNReal.ofReal_ne_top).ne'
    have hF0 : ∀ z ∈ OmF X x0, F z = 0 := by
      intro z0 hz0
      by_contra hne
      have hev1 : ∀ᶠ y in 𝓝 z0, y ∈ OmF X x0 := hU.mem_nhds hz0
      have hev : ∀ᶠ y in 𝓝 z0, y ∈ OmF X x0 ∧ F y ≠ 0 :=
        hev1.and ((hF.continuousOn.continuousAt (hU.mem_nhds hz0)).eventually_ne hne)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
      have hsub : Metric.ball z0 ε ⊆ OmF X x0 := fun y hy => (hball y hy).1
      have htop : ∫⁻ y in Metric.ball z0 ε, ENNReal.ofReal (densF X x0 y) *
          (ENNReal.ofReal (‖F y‖ ^ 2 / kaF X x0 bb y) * WSk X Xa Fl (cpt X x0 y)) = ⊤ := by
        rw [setLIntegral_congr_fun measurableSet_ball (g := fun _ => ⊤) fun y hy => ?_,
          setLIntegral_const, ENNReal.top_mul (Metric.measure_ball_pos volume z0 hε).ne']
        have hyO := hsub hy
        have ha : ENNReal.ofReal (densF X x0 y) ≠ 0 := (ENNReal.ofReal_pos.mpr (OntoB.densF_pos hyO)).ne'
        have hb : ENNReal.ofReal (‖F y‖ ^ 2 / kaF X x0 bb y) ≠ 0 := by
          refine (ENNReal.ofReal_pos.mpr (div_pos ?_ (Real.exp_pos _))).ne'
          have := (hball y hy).2; positivity
        rw [hWtop y hyO, ENNReal.mul_top hb, ENNReal.mul_top ha]
      have := lt_of_le_of_lt (lintegral_mono_set hsub) hInU
      rw [htop] at this
      exact lt_irrefl _ this
    refine ⟨fun _ _ => 0, fun α _ => ⟨differentiableOn_const _, ?_⟩, fun z hz => ?_⟩
    · unfold InAt; simp
    · rw [hF0 z hz]; simp

  obtain ⟨k1, z1, hz1, hk1⟩ := hex
  set g1 : V (nd X) → ℂ := fun z => Fl.s k1 (cpt X x0 z) with hg1def
  have hg1 : DifferentiableOn ℂ g1 (OmF X x0) := OntoB.hol_comp X x0 (Fl.s_van k1).1.1.1.1
  have hg10 : ∃ z ∈ OmF X x0, g1 z ≠ 0 := ⟨z1, hz1, hk1⟩
  set U' : Set (V (nd X)) := {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} with hU'def
  have hU'o : IsOpen U' := ExG.isOpen_Om X x0 g1 hg1
  obtain ⟨S, hSz, -⟩ := exhaustG_holds r X x0 ho g1 hg1
  set sv : Fin (nd X) → V (nd X) → ℂ := fun k z => Fl.s k (cpt X x0 z) with hsv
  have hsvO : ∀ k, DifferentiableOn ℂ (sv k) (OmF X x0) := fun k =>
    OntoB.hol_comp X x0 (Fl.s_van k).1.1.1.1
  have hsvd : ∀ k, DifferentiableOn ℂ (sv k) U' := fun k => (hsvO k).mono fun z hz => hz.1
  have hnz : ∀ y ∈ U', ∃ i, sv i y ≠ 0 := fun y hy => ⟨k1, hy.2⟩
  have hph : ContDiffOn ℝ ∞ (ph0 X Xa x0 bb) U' :=
    (UpDivE.plurisubharmonicWeight_smooth X Xa x0 bb).mono fun z hz => hz.1
  have hl : ∀ y ∈ U', ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ (leviV (nd X) (fun w => ((ph0 X Xa x0 bb w : ℝ) : ℂ)) y ξ).re :=
    fun y hy ξ => UpDivE.leviForm_weight_nonneg X Xa x0 bb hbm ho (hmar x0 ho) hy.1 ξ
  have hSs : ∀ y ∈ U', 0 < Ss X Xa Fl x0 y := fun y hy =>
    Finset.sum_pos' (fun _ _ => by positivity) ⟨k1, Finset.mem_univ _, by have := hy.2; positivity⟩
  have hI : ∫⁻ y in U', ENNReal.ofReal (‖F y‖ ^ 2 * (∑ i, ‖sv i y‖ ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2)) *
      Real.exp (-ph0 X Xa x0 bb y)) < ⊤ := by
    refine lt_of_le_of_lt ?_ hInU
    calc ∫⁻ y in U', ENNReal.ofReal (‖F y‖ ^ 2 * (∑ i, ‖sv i y‖ ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2)) *
          Real.exp (-ph0 X Xa x0 bb y))
        = ∫⁻ y in U', ENNReal.ofReal (densF X x0 y) *
            (ENNReal.ofReal (‖F y‖ ^ 2 / kaF X x0 bb y) * WSk X Xa Fl (cpt X x0 y)) := by
          refine setLIntegral_congr_fun hU'o.measurableSet fun y hy => ?_
          exact (wSk_eq X Xa Fl x0 bb hy.1 (hSs y hy) F).symm
      _ ≤ _ := lintegral_mono_set fun y hy => hy.1
  have hcond : ((nd X : ℕ) : ℝ) - 1 < (Xa.T : ℝ) - 1 / 2 - ((Xa.T - nd X : ℕ) : ℝ) - 1 + 1 := by
    rw [Nat.cast_sub hTn]; linarith
  obtain ⟨H, hH, hid⟩ := UpDivB.iter_div hU'o S hSz sv (ph0 X Xa x0 bb) hn2 hsvd hnz hph hl
    ((Xa.T : ℝ) - 1 / 2) (Xa.T - nd X) hcond F (hF.mono fun z hz => hz.1) hI
  have hexp : ((Xa.T : ℝ) - 1 / 2 - ((Xa.T - nd X : ℕ) : ℝ)) = (nd X : ℝ) - 1 / 2 := by
    rw [Nat.cast_sub hTn]; ring
  have hSc : ContinuousOn (Ss X Xa Fl x0) (OmF X x0) :=
    continuousOn_finsetSum _ fun k _ => ((hsvO k).continuousOn.norm).pow 2
  have hpc : ContinuousOn (ph0 X Xa x0 bb) (OmF X x0) := (UpDivE.plurisubharmonicWeight_smooth X Xa x0 bb).continuousOn
  have hω : ∀ K ⊆ OmF X x0, IsCompact K → ∃ c > 0, ∀ y ∈ K ∩ U',
      c ≤ (∑ i, ‖sv i y‖ ^ 2) ^ (-((nd X : ℝ) - 1 / 2)) * Real.exp (-ph0 X Xa x0 bb y) := by
    intro K hKU hK
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hSc.mono hKU)
    obtain ⟨P, hP⟩ := hK.exists_bound_of_continuousOn (hpc.mono hKU)
    refine ⟨(max M 1) ^ (-((nd X : ℝ) - 1 / 2)) * Real.exp (-P), by positivity, fun y hy => ?_⟩
    have hsy := hSs y hy.2
    have hle : Ss X Xa Fl x0 y ≤ max M 1 := by
      have := hM y hy.1
      rw [Real.norm_of_nonneg hsy.le] at this
      exact this.trans (le_max_left _ _)
    have ha : (0 : ℝ) ≤ (nd X : ℝ) - 1 / 2 := by
      have : (2 : ℝ) ≤ nd X := by exact_mod_cast hn2
      linarith
    have h1 : (max M 1) ^ (-((nd X : ℝ) - 1 / 2)) ≤ (Ss X Xa Fl x0 y) ^ (-((nd X : ℝ) - 1 / 2)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg hsy.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hsy _) (Real.rpow_le_rpow hsy.le hle ha)
    have h2 : Real.exp (-P) ≤ Real.exp (-ph0 X Xa x0 bb y) := by
      refine Real.exp_le_exp.mpr ?_
      have := hP y hy.1
      have := le_abs_self (ph0 X Xa x0 bb y)
      rw [Real.norm_eq_abs] at *
      linarith
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (Real.rpow_nonneg hsy.le _)
  have hext : ∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), ∃ H' : V (nd X) → ℂ,
      DifferentiableOn ℂ H' (OmF X x0) ∧ EqOn H' (H α) U' := by
    intro α hα
    have hIα : ∫⁻ y in U', ENNReal.ofReal (‖H α y‖ ^ 2 *
        ((∑ i, ‖sv i y‖ ^ 2) ^ (-((nd X : ℝ) - 1 / 2)) * Real.exp (-ph0 X Xa x0 bb y))) < ⊤ := by
      have := (hH α hα).2
      rw [hexp] at this
      simpa only [mul_assoc] using this
    have hloc := UpDivF.loc_int hU hU'o (g := g1) (fun y => Iff.rfl) (hH α hα).1.continuousOn hω hIα
    exact UpDivC.ext_glue hU hUc hg1 hg10 (hH α hα).1 hloc
  choose! Hx hHxd hHxeq using hext
  refine ⟨Hx, fun α hα => ⟨hHxd α hα, ?_⟩, fun z hz => ?_⟩
  · unfold InAt
    rw [IW.muF_lintegral]
    have hnull := UpDivF.zero_null hU hUc hg1 hg10
    have hae : (OmF X x0 : Set (V (nd X))) =ᵐ[volume] U' := by
      refine ae_eq_set.mpr ⟨?_, ?_⟩
      · refine measure_mono_null (fun y hy => ?_) hnull
        refine ⟨hy.1, ?_⟩
        by_contra h
        exact hy.2 ⟨hy.1, h⟩
      · have : U' \ OmF X x0 = ∅ := by
          ext y; simp only [Set.mem_sdiff, mem_empty_iff_false, iff_false]
          exact fun h => h.2 h.1.1
        rw [this, measure_empty]
    rw [setLIntegral_congr hae]
    have hn12 : (1 / 2 : ℝ) ≤ (nd X : ℝ) := by
      have : (2 : ℝ) ≤ nd X := by exact_mod_cast hn2
      linarith
    calc ∫⁻ y in U', ENNReal.ofReal (densF X x0 y) *
          (ENNReal.ofReal (‖Hx α y‖ ^ 2 / kaF X x0 bb y) * weightFunctionOnFrames X Xa (cpt X x0 y))
        ≤ ∫⁻ y in U', ENNReal.ofReal (Cs ^ ((nd X : ℝ) - 1 / 2) * Cw ^ (1 / 2 : ℝ)) *
            ENNReal.ofReal (‖H α y‖ ^ 2 * Ss X Xa Fl x0 y ^ (-((nd X : ℝ) - 1 / 2)) *
              Real.exp (-ph0 X Xa x0 bb y)) := by
          refine setLIntegral_mono' hU'o.measurableSet fun y hy => ?_
          rw [hHxeq α hα hy]
          exact weightedDensity_bound X Xa Fl x0 bb hy.1 (hSs y hy) (H α) (hCs _ hy.1) (hCw _ hy.1) hn12
      _ < ⊤ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
          have := (hH α hα).2
          rw [hexp] at this
          exact this
  · have hcont : ContinuousOn (fun z => F z - ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X),
        (∏ k, Fl.s k (cpt X x0 z) ^ α k) * Hx α z) (OmF X x0) := by
      refine hF.continuousOn.sub (continuousOn_finsetSum _ fun α hα => ?_)
      exact (continuousOn_finsetProd _ fun k _ => ((hsvO k).continuousOn.pow _)).mul
        (hHxd α hα).continuousOn
    have h0 := UpDivF.eq_across hU hUc hg1 hg10 hcont (fun y hy hgy => by
      have hy' : y ∈ U' := ⟨hy, hgy⟩
      rw [hid y hy', sub_eq_zero]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [hHxeq α hα hy']) z hz
    exact sub_eq_zero.mp h0

end ReciprocityTheory.ChartRestriction.G.AR.Up
