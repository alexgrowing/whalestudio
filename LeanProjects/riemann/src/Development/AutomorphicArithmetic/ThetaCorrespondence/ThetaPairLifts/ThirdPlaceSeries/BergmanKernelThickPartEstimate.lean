import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BergmanKernelThickPartEstimate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DividedWeightStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ

set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.ThickBerg
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory
set_option maxHeartbeats 4000000 in
theorem exp_neg_B_le_bergOn_of_mem_framesOn : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ B : ℝ, 0 ≤ B ∧ lenT p i PP * B ≤ C * unitE p ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Fm.L x ι).sc.b ≤ (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 → ENNReal.ofReal (Real.exp (-B)) ≤ bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  intro _ _ _ hS _
  obtain ⟨C0, hC0, hpeak⟩ := GlobalTheory.T.exists_cusp_form_peak_at_injective_chart_frame
  have hnum := _root_.GlobalTheory.T.torus_length_lower_bound_quotient' hS
  refine (((hnum.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt (max 10 C0))).and _root_.GlobalTheory.CovTop.WtShape.wtN_z).and hS).imp
    fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨C2, hC2, hN⟩, ⟨A, -, hH⟩⟩, ⟨C3, -, hW⟩⟩, ⟨C4, -, hSz⟩⟩ := h
  refine ⟨C0 * (C2 + 1), by positivity, ?_⟩
  obtain ⟨x0, hall⟩ := ((hN.and hH).and hW).and hSz
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY u1 hu1 => ?_⟩
  obtain ⟨⟨⟨hN, hH⟩, hW⟩, hSz⟩ := hall x hx hle ι p hp
  obtain ⟨hZ24, hu⟩ := hN i hi
  obtain ⟨hTl1, hgap⟩ := hu u1 hu1
  have hHi := hH i
  have hWi := hW i
  have hSi := hSz i
  have hsig := hWi.sig
  have hm3 := (Fm.D x ι).R.m_add_three_le_k
  simp only [Ranks.sigW] at hsig
  have hp1 : 1 ≤ (dat p i).p := by omega
  have hq1 : 1 ≤ (dat p i).q := by omega
  have hf1 : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by have := hHi.f8; omega : 1 ≤ (Fm.D x ι).R.f)
  have hr1 : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r)
  have hD1 : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ) := by
    rw [hWi.dim]
    have h2 : 1 ≤ (Fm.D x ι).R.r.choose 2 := Nat.choose_pos (by omega)
    have h8 := hHi.f8
    exact_mod_cast (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))
  have hzb : zBase (Fm.L x ι) = ((Fm.D x ι).R.f * (Fm.D x ι).R.r) * (Fm.L x ι).sc.L := rfl
  obtain ⟨hA8, hC08, h100⟩ := nums ((Fm.D x ι).R.f * (Fm.D x ι).R.r) (Fm.L x ι).sc.L C0 _ _ _ _ _
    (one_le_mul_of_one_le_of_one_le hf1 hr1) hHi.big.2.1 ((le_max_right _ _).trans hHi.big.1)
    (hzb ▸ hHi.ppLow) (hzb ▸ hZ24) hD1 hWi.what₂.2 hSi.2.1
  have hl10 : 0 ≤ l1 u1 := by unfold l1; positivity
  refine ⟨C0 * (l1 u1 + ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ^ 8), by positivity, ?_, fun Z σ hσ y hy hb => ?_⟩
  · have e : (lenT p i (Fm.parT x hx ι).PP : ℝ) * (C0 * (l1 u1 + ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ^ 8)) =
        C0 * ((lenT p i (Fm.parT x hx ι).PP : ℝ) * l1 u1 + (lenT p i (Fm.parT x hx ι).PP : ℝ) * ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ^ 8) := by ring
    rw [e, mul_add C0 C2 1, mul_one]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hTl1 hA8) hC0]
  · have hL := GlobalTheory.LawsDeep.levLaws _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
    have hg0 : ∀ q : ℕ, q.Prime → p.T.Q.l.GoodAt q :=
      Formalism.L2.Pj.goodAt_of_two_primes p.fw.laws.pins.2.1.1 ((Fm.D x ι).host.g_prime 0) ((Fm.D x ι).host.g_prime 1)
        (Fm.D x ι).host.g_ne
    have hg : ∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hY.1.lev.1.2.1 hg0
    have hU := hL.unf σ hσ
    have hM' : Y.d.l₂.M' = Y.d.l₂.M := by rw [Level.M', hY.1.lev.2, Nat.lcm_one_right]
    refine GlobalTheory.T.cuspForm_lower_bound_bergmanFunction_on_component (Fm.D x ι) ((i : ℕ) + 1) _ _ _ Y.d.Xo₂ Y.d.c₂ Y.U Y.dict hL σ hσ _ Z y hy _
      (fun x0 FF hx0 hFF => ?_)
    obtain ⟨x1, hx1, hla, htr⟩ := orth_transfer _ _ ((Y.U σ).X y.1)
      (modelWt (Y.U σ) (wtOf (dat p i) u1 0) y.1) y.2.1 y.2.2
    obtain ⟨hg1, hg2, hl1, hcard⟩ := modelWt_shape _ _ _ _ _ _ σ _ (Y.U σ) hσ hU hp1 hq1 u1
      (lenT p i (Fm.parT x hx ι).PP) (fun τ a b hab => by exact_mod_cast hgap τ a b hab) y.1
    have hcf : (((Y.U σ).X y.1).Ψ.card : ℝ) = (Fm.D x ι).R.f := by
      rw [hcard]; exact_mod_cast hWi.card
    have hball := ball_injects _ _ _ _ _ _ σ _ (Y.U σ) hσ hU hg hp1 hq1 y.1 x1 hx1 (by
      rw [hcf, hM', hla]; exact h100.trans hb)
    have hp0 := (hU.2.1 y.1).1
    have hr := hU.1
    obtain ⟨P, hP, hPx, hle⟩ := hpeak _ _ ((Y.U σ).X y.1) (modelWt (Y.U σ) (wtOf (dat p i) u1 0) y.1) x1
      (by rw [hp0]; exact hq1) (by rw [hp0, hr]; exact Nat.lt_add_of_pos_left hp1) hx1
      (fun τ a b hab hb0 => by rw [hcf]; exact hC08.trans (hg1 τ a b hab hb0))
      (fun τ a b ha hb' => by rw [hcf]; exact hC08.trans (hg2 τ a b ha hb')) hball x0 FF hx0 hFF
    obtain ⟨hPy, hpn⟩ := htr P hP hPx
    refine ⟨P, hP, hPy, ?_⟩
    rw [hpn]
    rw [hl1, hcf] at hle
    exact hle
end GlobalTheory.ThickBerg
end
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_neg_B_le_bergOn_of_la1sq_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ B : ℝ, 0 ≤ B ∧ lenT p i PP * B ≤ C * unitE p ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Fm.L x ι).sc.b ≤ (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 → ENNReal.ofReal (Real.exp (-B)) ≤ bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  first | exact @_root_.GlobalTheory.ThickBerg.exp_neg_B_le_bergOn_of_mem_framesOn | exact _root_.GlobalTheory.ThickBerg.exp_neg_B_le_bergOn_of_mem_framesOn | (intros; apply _root_.GlobalTheory.ThickBerg.exp_neg_B_le_bergOn_of_mem_framesOn <;> assumption)
end
end
