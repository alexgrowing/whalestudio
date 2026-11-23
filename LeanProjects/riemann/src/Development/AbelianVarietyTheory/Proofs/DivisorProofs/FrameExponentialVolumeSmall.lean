import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPeakAtInjectiveChartFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepCongruenceElementSeparatesChartBallThickFramStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualAndPrincipalCongruenceOrbitsOfGoodLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLowerBoundBergmanFunctionOnComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLengthLowerBoundQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitriangularChartMemDomainSmallBallStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelWeightGapL1CardBoundStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ThickBerg

open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

theorem cpt_mem_dom_small : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), IsOrth X x → ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) →
    cpt X x z ∈ X.dom := GlobalTheory.T.unitriangularChart_mem_domain_small_ball

theorem ball_injects : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r),
    GoodEmb c σ → IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q →
    ∀ (k : U.Comp) (x : Frame (U.X k).Ψ r), IsOrth (U.X k) x →
    100 * (((U.X k).Ψ.card : ℝ) * r) ^ 4 ≤ (l.M' : ℝ) * (U.X k).firstMinimumSq x →
    ∀ γ ∈ (U.X k).Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (nd (U.X k)), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) →
      ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor (U.X k).Ψ r,
      lact γ (cpt (U.X k) x z) = rmul (cpt (U.X k) x z') b → γ = 1 := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hl hp hq k x hx hM γ hγ z z' hz hz' b hb he
  obtain ⟨hsd, horb⟩ := GlobalTheory.T.selfDual_and_principalCongruence_orbits_of_goodLevel E H Dw l Xo c σ r U hσ hU hl hp hq k
  have hwd : cpt (U.X k) x z ∈ (U.X k).dom := cpt_mem_dom_small E r (U.X k) x z hx hz
  obtain ⟨γ', hγ'U, hγ'c, b', hb', he'⟩ := horb γ hγ _ hwd
  have h1 : lact γ' (cpt (U.X k) x z) =
      rmul (cpt (U.X k) x z') (rmul b (ExtFPf.invF (U.X k) b')) := by
    have e1 := congrArg (fun w => rmul w (ExtFPf.invF (U.X k) b')) (he'.symm.trans he)
    simp only [ExtFPf.rmul_assoc, ExtFPf.rmul_invF _ hb', ExtFPf.rmul_oneF] at e1
    exact e1
  have hγ'1 : γ' = 1 := GlobalTheory.T.deep_congruence_element_separates_chart_ball_thick_frame E r (U.X k) l.M' x hsd hx hM γ' hγ'U hγ'c z z' hz hz' _
    (ExtFPf.mul_mem _ hb (ExtFPf.invF_mem _ hb')) h1
  subst hγ'1
  rw [FundSetPf.lact_one] at he'
  exact (U.X k).Γ_free γ hγ _ hwd b' hb' he'

theorem modelWt_shape : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r),
    GoodEmb c σ → IsUnf U → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (u1 : GlobalTheory.AllWt.Weight Dw) (g : ℝ),
    (∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 → g ≤ (u1 τ a : ℝ) - u1 τ b) → ∀ k : U.Comp,
    (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ (U.X k).p0 →
      g ≤ (modelWt U (wtOf Dw u1 0) k τ a : ℝ) - modelWt U (wtOf Dw u1 0) k τ b) ∧
    (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 →
      g ≤ (modelWt U (wtOf Dw u1 0) k τ b : ℝ) - modelWt U (wtOf Dw u1 0) k τ a) ∧
    (∑ τ, ∑ a, |(modelWt U (wtOf Dw u1 0) k τ a : ℝ)|) = l1 u1 ∧
    (U.X k).Ψ.card = Nat.card (Psi H) := GlobalTheory.T.model_weight_gap_l1_card_bound

theorem orth_transfer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (y : Frame X.Ψ r), y ∈ X.dom → ∃ x, IsOrth X x ∧ X.firstMinimumSq x = X.firstMinimumSq y ∧
    ∀ P ∈ X.SS la, P x ≠ 0 → P y ≠ 0 ∧ X.pnorm la P y = X.pnorm la P x := by
  intro E _ _ _ r X la y hy
  obtain ⟨x, hx, b, hb, rfl⟩ := ReciprocityTheory.ChartRestriction.G.AR.Up.ortho_holds r X y hy
  have hxd := ReciprocityTheory.ChartRestriction.G.AR.Up.KU.orth_dom X hx
  refine ⟨x, hx, (firstMinimumSq_rightBorel X hxd hb).symm, fun P hP hPx =>
    ⟨?_, FrameDegreeData.pnorm_rmul X la P hP.1.1.2.1 x hxd b hb⟩⟩
  rw [hP.1.1.2.1 x hxd b hb]
  refine mul_ne_zero ?_ hPx
  unfold bchar
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  have h := (hb τ).1
  rw [Matrix.det_of_upperTriangular ((ExtFPf.upper_iff X b τ).mp (hb τ).2)] at h
  exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)

theorem nums (a l C0 PP T D b uE : ℝ) (ha : 1 ≤ a) (hl : 10 ≤ l) (hlC : C0 ≤ l) (hPP : (a * l) ^ 12 ≤ PP)
    (hT : (a * l) ^ 24 ≤ T) (hD : 1 ≤ D) (hrows : PP * T * D ^ 2 * l ≤ b) (hbu : b ≤ uE) :
    T * a ^ 8 ≤ uE ∧ C0 * a ^ 8 ≤ T ∧ 100 * a ^ 4 ≤ b := by
  have h1 : 1 ≤ a * l := by nlinarith
  have hal8 : a ^ 8 ≤ (a * l) ^ 12 :=
    calc a ^ 8 ≤ (a * l) ^ 8 := pow_le_pow_left₀ (by linarith) (by nlinarith) 8
      _ ≤ (a * l) ^ 12 := pow_le_pow_right₀ h1 (by norm_num)
  have hPP' : a ^ 8 ≤ PP := hal8.trans hPP
  have hT1 : 1 ≤ T := (one_le_pow₀ h1).trans hT
  have hPP0 : 0 ≤ PP := (by positivity : (0 : ℝ) ≤ a ^ 8).trans hPP'
  have hDl : 1 ≤ D ^ 2 * l := by nlinarith [one_le_pow₀ (n := 2) hD]
  have hTPP : T * PP ≤ b := by
    have h2 : T * PP ≤ PP * T * D ^ 2 * l := by
      have h3 : 0 ≤ PP * T := mul_nonneg hPP0 (by linarith)
      nlinarith
    linarith
  refine ⟨?_, ?_, ?_⟩
  · calc T * a ^ 8 ≤ T * PP := mul_le_mul_of_nonneg_left hPP' (by linarith)
      _ ≤ uE := hTPP.trans hbu
  · have h4 : a ^ 8 * l ≤ (a * l) ^ 24 := by
      rw [mul_pow]
      exact mul_le_mul (pow_le_pow_right₀ ha (by norm_num)) (le_self_pow₀ (by linarith) (by norm_num))
        (by linarith) (by positivity)
    have h5 : C0 * a ^ 8 ≤ l * a ^ 8 := mul_le_mul_of_nonneg_right hlC (by positivity)
    linarith
  · have h12 : 100 * a ^ 4 ≤ (a * l) ^ 12 := by
      rw [mul_pow]
      have h6 : (100 : ℝ) ≤ l ^ 12 :=
        calc (100 : ℝ) ≤ 10 ^ 12 := by norm_num
          _ ≤ l ^ 12 := pow_le_pow_left₀ (by norm_num) hl 12
      have h7 : a ^ 4 ≤ a ^ 12 := pow_le_pow_right₀ ha (by norm_num)
      have h8 : 0 ≤ a ^ 4 := by positivity
      nlinarith
    have h9 : PP ≤ T * PP := le_mul_of_one_le_left hPP0 hT1
    linarith

set_option maxHeartbeats 4000000 in
theorem thick_bound : Hypotheses2 → HypothesesH → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ B : ℝ, 0 ≤ B ∧ lenT p i PP * B ≤ C * unitE p ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Fm.L x ι).sc.b ≤ (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 → ENNReal.ofReal (Real.exp (-B)) ≤ bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  intro _ _ _ hS _
  obtain ⟨C0, hC0, hpeak⟩ := GlobalTheory.T.exists_cusp_form_peak_at_injective_chart_frame
  have hnum := GlobalTheory.T.torus_length_lower_bound_quotient hS
  refine (((hnum.and (GlobalTheory.CovTop.Sizes.hostN (max 10 C0))).and GlobalTheory.CovTop.WtShape.wtN).and hS).imp
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
