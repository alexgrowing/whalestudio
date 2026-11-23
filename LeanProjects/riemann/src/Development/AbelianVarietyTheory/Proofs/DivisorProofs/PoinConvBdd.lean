import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

namespace GlobalTheory.PoinSumBound

open Topology Filter ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open scoped Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def SumBd (X : Data E r) (x0 : Frame X.Ψ r) (s : ℝ) : Prop :=
  ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x →
    ∑' γ : X.Γ, ENNReal.ofReal (Real.exp (-(s * GlobalTheory.Up.rhX X x0 (lact γ.1 x)))) ≤ C

def HypS (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ) : Prop :=
  IsOrth X x0 ∧ PropDisc X ∧ IsMetricW X la W ∧ WLower X la W ∧
    (0 < bb ∧ SumBd X x0 (bb / 2)) ∧ DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧
    IsBEq X la P ∧ ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z

theorem kaY_eq_exp (X : Data E r) {x0 y : Frame X.Ψ r} (h0 : IsOrth X x0) (hy : y ∈ X.dom) (s : ℝ) :
    kaY X x0 s y = Real.exp (-(s * GlobalTheory.Up.rhX X x0 y)) := by
  unfold kaY
  congr 1
  rw [GlobalTheory.Up.rhX_eq_sum h0 hy]
  unfold rhY
  simp only [Real.log_pow, i0, gM]
  rw [Finset.sum_sub_distrib]
  push_cast
  ring

theorem kaSum_of (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) {s : ℝ} (h : SumBd X x0 s) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x →
      ∑' γ : X.Γ, ENNReal.ofReal (kaY X x0 s (lact γ.1 x)) ≤ C := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun x hx => le_trans (le_of_eq (tsum_congr fun γ => ?_)) (hb x hx)⟩
  rw [kaY_eq_exp X hx0 (IW.orth_mem_dom X _ (PairUnfoldPf.isOrth_lact X γ.2 hx))]

end

end GlobalTheory.PoinSumBound

namespace GlobalTheory.PoinSumBound

open Topology Filter ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open scoped Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem sumBall (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ) (H : HypS X x0 la W bb F P) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ρ0 ≤ 1 ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, IsOrth X x →
      ∑' γ : X.Γ, (∫⁻ w in Bset X x ρ0,
        ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w))) ^ (1 / 2 : ℝ) ≤ C := by
  obtain ⟨hx0, -, hW, -, ⟨hbbpos, hSB⟩, -, hA, hP, hPF⟩ := H
  classical
  have hbb0 : 0 ≤ bb := hbbpos.le
  obtain ⟨ρ1, hρ1, hcomp⟩ := ka_comp X hx0 hbb0
  have e2 : ∀ᶠ w in 𝓝 (0 : V (nd X)), ∀ τ, ∀ i : Fin r, ‖lminor (Gw X w τ) i.castSucc‖ < 2 := by
    rw [Filter.eventually_all]; intro τ; rw [Filter.eventually_all]; intro i
    exact (cont_lminor X τ _).norm.continuousAt.eventually_lt continuousAt_const
      (by rw [norm_lminor_zero]; norm_num)
  obtain ⟨R2, hR2, hR2b⟩ := Metric.eventually_nhds_iff_ball.1 e2
  set ρ0 := min (min ρ1 R2) 1 with hρ0
  have hρ0pos : 0 < ρ0 := lt_min (lt_min hρ1 hR2) one_pos
  obtain ⟨C2, hC2, hsum⟩ := kaSum_of X hx0 hSB
  set K := Real.exp (bb * (3 * X.Ψ.card * Real.log 2)) with hK
  set cd : ℝ := ∏ _τ : X.Ψ, ∏ _i : Fin r, (1 / 4 : ℝ) with hcd
  have hcd0 : 0 < cd := Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => by norm_num
  set Nn := ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 with hNn
  set c0 : ℝ≥0∞ := ENNReal.ofReal K * ENNReal.ofReal (1 / cd) * Nn with hc0
  have hc0t : c0 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hA.ne
  have hψm := psiF_meas X x0 bb hP hW
  have hψB := psiF_rmul X hx0 bb hP hW
  refine ⟨ρ0, hρ0pos, min_le_right _ _, c0 ^ (1 / 2 : ℝ) * C2,
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hc0t) hC2, fun x hx hxo => ?_⟩
  have hI : ∀ γ : X.Γ, ∫⁻ w in Bset X x ρ0,
      ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w)) ≤
        c0 * ENNReal.ofReal (kaY X x0 bb (lact γ.1 x)) := by
    intro γ
    set x' := lact γ.1 x with hx'
    have hx'o : IsOrth X x' := PairUnfoldPf.isOrth_lact X γ.2 hxo
    have hcptl : ∀ w, lact γ.1 (cpt X x w) = cpt X x' w := fun w =>
      (PairUnfoldPf.cpt_lact X γ.1 x w).symm
    simp only [hcptl]
    have hdom : ∀ w ∈ Bset X x ρ0, cpt X x' w ∈ X.dom := fun w hw => by
      rw [← hcptl]; exact (PairUnfoldPf.lact_mem_dom_iff X γ.2 _).2 hw.2
    set A := ENNReal.ofReal K * ENNReal.ofReal (kaY X x0 bb x') * ENNReal.ofReal (1 / cd) with hAdef
    have hpt : ∀ w ∈ Bset X x ρ0, ‖P (cpt X x' w)‖ₑ ^ 2 * W (cpt X x' w) ≤
        A * (ENNReal.ofReal (densF X x' w) * psiF X x0 bb P W (cpt X x' w)) := by
      intro w hw
      have hyd := hdom w hw
      have hw1 : ‖w‖ < ρ1 := lt_of_lt_of_le hw.1 ((min_le_left _ _).trans (min_le_left _ _))
      have hw2 : w ∈ Metric.ball (0 : V (nd X)) R2 :=
        mem_ball_zero_iff.2 (lt_of_lt_of_le hw.1 ((min_le_left _ _).trans (min_le_right _ _)))
      have hka := hcomp x' hx'o w hw1
      have hdens : cd ≤ densF X x' w := by
        unfold densF
        refine Finset.prod_le_prod (fun _ _ => by positivity) fun τ _ =>
          Finset.prod_le_prod (fun _ _ => by norm_num) fun i _ => ?_
        rw [dmin_cpt_orth X hx'o]
        have h0 : 0 < ‖lminor (Gw X w τ) i.castSucc‖ := by
          rw [← dmin_cpt_orth X hx'o]; exact norm_pos_iff.2 (dmin_ne X hyd τ _)
        have h2 := hR2b w hw2 τ i
        rw [zpow_neg, zpow_ofNat, show (1 / 4 : ℝ) = ((2 : ℝ) ^ 2)⁻¹ by norm_num]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h0.le h2.le 2)
      have hden : 1 ≤ ENNReal.ofReal (1 / cd) * ENNReal.ofReal (densF X x' w) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [one_div_mul_eq_div, le_div_iff₀ hcd0]
        linarith
      have hkk : ENNReal.ofReal (kaY X x0 bb (cpt X x' w)) ≤
          ENNReal.ofReal K * ENNReal.ofReal (kaY X x0 bb x') := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]; exact ENNReal.ofReal_le_ofReal hka
      rw [← psiF_mul X x0 bb P W hyd]
      calc psiF X x0 bb P W (cpt X x' w) * ENNReal.ofReal (kaY X x0 bb (cpt X x' w))
          ≤ psiF X x0 bb P W (cpt X x' w) * (ENNReal.ofReal K * ENNReal.ofReal (kaY X x0 bb x')) :=
            mul_le_mul_of_nonneg_left hkk zero_le
        _ = psiF X x0 bb P W (cpt X x' w) * (ENNReal.ofReal K * ENNReal.ofReal (kaY X x0 bb x')) * 1 :=
            (mul_one _).symm
        _ ≤ psiF X x0 bb P W (cpt X x' w) * (ENNReal.ofReal K * ENNReal.ofReal (kaY X x0 bb x')) *
              (ENNReal.ofReal (1 / cd) * ENNReal.ofReal (densF X x' w)) :=
            mul_le_mul_of_nonneg_left hden zero_le
        _ = A * (ENNReal.ofReal (densF X x' w) * psiF X x0 bb P W (cpt X x' w)) := by
            rw [hAdef]; ring
    have hsub : Bset X x ρ0 ⊆ OmF X x' := fun w hw => hdom w hw
    have hAt : A ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
    calc ∫⁻ w in Bset X x ρ0, ‖P (cpt X x' w)‖ₑ ^ 2 * W (cpt X x' w)
        ≤ ∫⁻ w in Bset X x ρ0, A * (ENNReal.ofReal (densF X x' w) * psiF X x0 bb P W (cpt X x' w)) :=
          setLIntegral_mono' (isOpen_Bset X x ρ0).measurableSet hpt
      _ = A * ∫⁻ w in Bset X x ρ0, ENNReal.ofReal (densF X x' w) * psiF X x0 bb P W (cpt X x' w) :=
          lintegral_const_mul' _ _ hAt
      _ ≤ A * ∫⁻ w in OmF X x', ENNReal.ofReal (densF X x' w) * psiF X x0 bb P W (cpt X x' w) :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set hsub) zero_le
      _ = A * ∫⁻ w, psiF X x0 bb P W (cpt X x' w) ∂muF X x' := by
          have hm : Measurable fun w => psiF X x0 bb P W (cpt X x' w) :=
            hψm.comp (cont_cpt' X x').measurable
          rw [muF, lintegral_withDensity_eq_lintegral_mul _ (meas_densF' X x') hm]
          rfl
      _ = A * Nn := by
          rw [measInv_holds r X x' x0 hx'o hx0 _ hψm hψB, psiF_int X hx0 bb hPF]
      _ = c0 * ENNReal.ofReal (kaY X x0 bb x') := by rw [hAdef, hc0]; ring
  calc ∑' γ : X.Γ, (∫⁻ w in Bset X x ρ0,
        ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w))) ^ (1 / 2 : ℝ)
      ≤ ∑' γ : X.Γ, (c0 * ENNReal.ofReal (kaY X x0 bb (lact γ.1 x))) ^ (1 / 2 : ℝ) :=
        ENNReal.tsum_le_tsum fun γ => ENNReal.rpow_le_rpow (hI γ) (by norm_num)
    _ = ∑' γ : X.Γ, c0 ^ (1 / 2 : ℝ) * ENNReal.ofReal (kaY X x0 (bb / 2) (lact γ.1 x)) :=
        tsum_congr fun γ => by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), kaY_half]
    _ = c0 ^ (1 / 2 : ℝ) * ∑' γ : X.Γ, ENNReal.ofReal (kaY X x0 (bb / 2) (lact γ.1 x)) :=
        ENNReal.tsum_mul_left
    _ ≤ c0 ^ (1 / 2 : ℝ) * C2 := mul_le_mul_of_nonneg_left (hsum x hxo) zero_le

end

end GlobalTheory.PoinSumBound

namespace GlobalTheory.PoinSumBound

open Topology Filter ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open scoped Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ballB (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ) (H : HypS X x0 la W bb F P)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) : ∃ C : ℝ, ∀ x ∈ X.dom, IsOrth X x →
      ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ ≤ ENNReal.ofReal C * supR X la W ρ x := by
  obtain ⟨ρ0, hρ0, hρ01, CB, hCB, hS'⟩ := sumBall X x0 la W bb F P H
  set ρ' := min ρ ρ0 with hρ'
  obtain ⟨CA, hCA, hA'⟩ := (subMean_holds (E := E)) r X la ρ' (lt_min hρ hρ0) ((min_le_left _ _).trans hρ1)
  obtain ⟨-, -, hW, ⟨c, hc, hcW⟩, -, -, -, hP, -⟩ := H
  refine ⟨(CA ^ (1 / 2 : ℝ) * CB).toReal, fun x hx hxo => ?_⟩
  rw [ENNReal.ofReal_toReal (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCA.ne) hCB.ne)]
  have hsum := hS' x hx hxo
  set I : X.Γ → ℝ≥0∞ := fun γ => ∫⁻ w in Bset X x ρ0,
    ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w)) with hIdef
  set I' : X.Γ → ℝ≥0∞ := fun γ => ∫⁻ w in Bset X x ρ',
    ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w)) with hI'def
  have hII : ∀ γ, I' γ ≤ I γ := fun γ => lintegral_mono_set (Bset_mono X x (min_le_right _ _))
  have hIfin : ∀ γ, I γ ≠ ⊤ := by
    intro γ h
    have h1 : I γ ^ (1 / 2 : ℝ) ≤ CB := (ENNReal.le_tsum γ).trans hsum
    rw [h, ENNReal.top_rpow_of_pos (by norm_num)] at h1
    exact hCB.ne (top_le_iff.1 h1)
  have hterm : ∀ γ : X.Γ, ‖P (lact γ.1 x)‖ₑ ≤ CA ^ (1 / 2 : ℝ) * supR X la W ρ x * I γ ^ (1 / 2 : ℝ) := by
    intro γ
    have hPγ : DifferentiableOn ℂ (fun y => P (lact γ.1 y)) X.dom :=
      hP.1.comp (differentiable_lact γ.1).differentiableOn fun y hy => lactDom X γ.2 hy
    have h1 := hA' _ hPγ x hx hxo
    have h2 := key_int X la W hW hc hcW P hP.1 γ.2 (ne_top_of_le_ne_top (hIfin γ) (hII γ))
    have h3 : ‖P (lact γ.1 x)‖ₑ ^ 2 ≤ CA * (supR X la W ρ x ^ 2 * I γ) := by
      refine h1.trans (mul_le_mul_of_nonneg_left (h2.trans ?_) zero_le)
      gcongr
      · exact supR_mono X la W (min_le_left _ _) x
      · exact hII γ
    calc ‖P (lact γ.1 x)‖ₑ = (‖P (lact γ.1 x)‖ₑ ^ 2) ^ (1 / 2 : ℝ) := (sq_pow_half _).symm
      _ ≤ (CA * (supR X la W ρ x ^ 2 * I γ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h3 (by norm_num)
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          sq_pow_half, mul_assoc]
  calc ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ
      ≤ ∑' γ, CA ^ (1 / 2 : ℝ) * supR X la W ρ x * I γ ^ (1 / 2 : ℝ) := ENNReal.tsum_le_tsum hterm
    _ = CA ^ (1 / 2 : ℝ) * supR X la W ρ x * ∑' γ, I γ ^ (1 / 2 : ℝ) := ENNReal.tsum_mul_left
    _ ≤ CA ^ (1 / 2 : ℝ) * supR X la W ρ x * CB := mul_le_mul_of_nonneg_left hsum zero_le
    _ = CA ^ (1 / 2 : ℝ) * CB * supR X la W ρ x := by ring

theorem locD (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ) (H : HypS X x0 la W bb F P) :
    ∀ x ∈ X.dom, ∃ ε > 0, ∃ u : X.Γ → ℝ, Summable u ∧
      ∀ γ : X.Γ, ∀ y ∈ Metric.ball x ε, ‖P (lact γ.1 y)‖ ≤ u γ := by
  intro x hx
  obtain ⟨ρ0, hρ0, hρ01, CB, hCB, hS'⟩ := sumBall X x0 la W bb F P H
  obtain ⟨-, -, hW, ⟨c, hc, hcW⟩, -, -, -, hP, -⟩ := H
  set b0 := FrameDegreeData.bOf X x with hb0def
  have hb0 : b0 ∈ Bor X.Ψ r := FrameDegreeData.bOf_mem X hx
  have ho : IsOrth X (rmul x b0) := FrameDegreeData.ortho_bOf X hx
  have hx1 : rmul x b0 ∈ X.dom := rmulDom X hb0 hx
  obtain ⟨ε, hε, CA, hCA, hA'⟩ := (subMeanLoc_of (lu_holds (E := E))) r X la ρ0 hρ0 hρ01 _ hx1 ho
  have hcont : Continuous fun y : Frame X.Ψ r => rmul y b0 := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    simp only [rmul, mat, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  obtain ⟨ε1, hε1, h1⟩ := Metric.continuousAt_iff.1 hcont.continuousAt ε hε
  obtain ⟨ε2, hε2, h2⟩ := Metric.isOpen_iff.1 (isOpenDom X) x hx
  set x1 := rmul x b0 with hx1def
  set I : X.Γ → ℝ≥0∞ := fun γ => ∫⁻ w in Bset X x1 ρ0,
    ‖P (lact γ.1 (cpt X x1 w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x1 w)) with hIdef
  set K : ℝ≥0∞ := (CA * ENNReal.ofReal (1 / c)) ^ (1 / 2 : ℝ) with hKdef
  have hK : K ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top hCA.ne ENNReal.ofReal_ne_top)
  have hsumfin : ∑' γ, K * I γ ^ (1 / 2 : ℝ) ≠ ⊤ := by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top hK (ne_top_of_le_ne_top hCB.ne (hS' _ hx1 ho))
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun γ => (K * I γ ^ (1 / 2 : ℝ)).toReal / ‖bchar la b0‖,
    (ENNReal.summable_toReal hsumfin).div_const _, fun γ y hy => ?_⟩
  have hyd : y ∈ X.dom := h2 (Metric.ball_subset_ball (min_le_right _ _) hy)
  have hyb : rmul y b0 ∈ Metric.ball x1 ε := h1 (Metric.ball_subset_ball (min_le_left _ _) hy)
  have hA1 := hA' _ (isBEq_lact X la hP γ.2) _ hyb
  have hint : ∫⁻ w in Bset X x1 ρ0, ‖P (lact γ.1 (cpt X x1 w))‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-phla X la (cpt X x1 w))) ≤ ENNReal.ofReal (1 / c) * I γ := by
    rw [hIdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' (isOpen_Bset X _ ρ0).measurableSet fun w hw => ?_
    rw [hW.2.2 γ.1 γ.2 _ hw.2]
    have he : ENNReal.ofReal (Real.exp (-phla X la (cpt X x1 w))) ≤
        ENNReal.ofReal (1 / c) * W (cpt X x1 w) := by
      calc ENNReal.ofReal (Real.exp (-phla X la (cpt X x1 w)))
          = ENNReal.ofReal (1 / c) * ENNReal.ofReal (c * Real.exp (-phla X la (cpt X x1 w))) := by
            rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (hcW _ hw.2) zero_le
    calc ‖P (lact γ.1 (cpt X x1 w))‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x1 w)))
        ≤ ‖P (lact γ.1 (cpt X x1 w))‖ₑ ^ 2 * (ENNReal.ofReal (1 / c) * W (cpt X x1 w)) :=
          mul_le_mul_of_nonneg_left he zero_le
      _ = _ := by ring
  have hB : ‖P (lact γ.1 (rmul y b0))‖ₑ ≤ K * I γ ^ (1 / 2 : ℝ) := by
    have h3 : ‖P (lact γ.1 (rmul y b0))‖ₑ ^ 2 ≤ CA * (ENNReal.ofReal (1 / c) * I γ) :=
      hA1.trans (mul_le_mul_of_nonneg_left hint zero_le)
    calc ‖P (lact γ.1 (rmul y b0))‖ₑ = (‖P (lact γ.1 (rmul y b0))‖ₑ ^ 2) ^ (1 / 2 : ℝ) :=
          (sq_pow_half _).symm
      _ ≤ (CA * (ENNReal.ofReal (1 / c) * I γ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h3 (by norm_num)
      _ = _ := by rw [← mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have heq : P (lact γ.1 (rmul y b0)) = bchar la b0 * P (lact γ.1 y) := by
    rw [lact_rmul', hP.2 _ (lactDom X γ.2 hyd) b0 hb0]
  have hbn : 0 < ‖bchar la b0‖ := norm_pos_iff.2 (bchar_ne X la hb0)
  rw [le_div_iff₀ hbn, mul_comm, ← norm_mul, ← heq]
  have hfin : K * I γ ^ (1 / 2 : ℝ) ≠ ⊤ := ne_top_of_le_ne_top hsumfin (ENNReal.le_tsum γ)
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 (by rw [ofReal_norm]; exact hB)

end

end GlobalTheory.PoinSumBound

open ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf in

theorem GlobalTheory.PoinSumBound.poin_conv_bdd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ), IsMetricW X la W → WLower X la W → 0 < bb → (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x → ∑' γ : X.Γ, ENNReal.ofReal (Real.exp (-(bb / 2 * GlobalTheory.Up.rhX X x0 (lact γ.1 x)))) ≤ C) → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) → InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) ∧ X.IsBddSec la (poin X la P) := by
  intro E _ _ _ r X x0 hx0 hPD la W bb hW hWl hbb hSB F P hFd hA hP hPF
  have H : GlobalTheory.PoinSumBound.HypS X x0 la W bb F P := ⟨hx0, hPD, hW, hWl, ⟨hbb, hSB⟩, hFd, hA, hP, hPF⟩
  obtain ⟨c, hc, hcW⟩ := hWl
  have hterm : ∀ (γ : X.Γ) y, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 y)‖ = ‖P (lact γ.1 y)‖ := by
    intro γ y; rw [norm_mul, norm_inv, PoinPf.norm_chi X la γ.2, inv_one, one_mul]
  obtain ⟨C1, hC1⟩ := GlobalTheory.PoinSumBound.ballB X x0 la W bb F P H 1 one_pos le_rfl
  have horth : ∀ y ∈ X.dom, IsOrth X y → ‖poin X la P y‖ ≤ max C1 0 * (1 / c) ^ (1 / 2 : ℝ) := by
    intro y hy hyo
    have h1 := (PoinPf.enorm_poin_le X la P y).trans ((hC1 y hy hyo).trans
      (mul_le_mul_of_nonneg_left (PoinPf.supR_le X la W hc hcW 1 y) (zero_le)))
    have h2 : ENNReal.ofReal C1 * ENNReal.ofReal (1 / c) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (max C1 0 * (1 / c) ^ (1 / 2 : ℝ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        ENNReal.ofReal_mul (le_max_right _ _)]
      gcongr
      exact le_max_left _ _
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h1.trans h2)
  refine ⟨?_, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · intro x hx
    obtain ⟨ε, hε, u, hu, hub⟩ := GlobalTheory.PoinSumBound.locD X x0 la W bb F P H x hx
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun γ => (hterm γ x).le.trans (hub γ x (Metric.mem_ball_self hε))) hu
  · unfold poin
    refine PoinPf.differentiableOn_tsum_loc (PoinPf.isOpenDom X) _ (fun γ => ?_) (fun x hx => ?_)
    · exact (differentiableOn_const _).mul
        (hP.1.comp (PoinPf.differentiable_lact γ.1).differentiableOn fun y hy => lactDom X γ.2 hy)
    · obtain ⟨ε, hε, u, hu, hub⟩ := GlobalTheory.PoinSumBound.locD X x0 la W bb F P H x hx
      exact ⟨ε, hε, u, hu, fun γ y hy => (hterm γ y).le.trans (hub γ y hy)⟩
  · intro x hx b hb
    exact poin_rmul X la P hP.2 hx hb
  · intro γ hγ x _
    exact poin_lact X la P hγ x
  · refine ⟨max C1 0 * (1 / c) ^ (1 / 2 : ℝ), fun x hx => ?_⟩
    have hb := FrameDegreeData.bOf_mem X hx
    have ho : IsOrth X (rmul x (FrameDegreeData.bOf X x)) := FrameDegreeData.ortho_bOf X hx
    have hxb : rmul x (FrameDegreeData.bOf X x) ∈ X.dom := rmulDom X hb hx
    rw [← FrameDegreeData.pnorm_rmul X la _ (fun y hy b hb => poin_rmul X la P hP.2 hy hb) x hx _ hb,
      PoinPf.pnorm_orth' X la _ ho]
    exact horth _ hxb ho
