import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.ToPotentialChartsChartFun
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli regMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts BoundedPshData pointReg pointCharts pointAtlas)

local notation "RegChartDataA" => GroundTheory.Heights₂.Heights.Regular.RegChartData

noncomputable section

theorem isClosed_coordDiv {D : ℕ} (S : Finset (Fin D)) : IsClosed (coordDiv S) := by
  have h : coordDiv S = ⋃ i ∈ S, (fun z : Fin D → ℂ => z i) ⁻¹' {0} := by
    ext z
    simp [coordDiv]
  rw [h]
  exact isClosed_biUnion_finset fun i _ => isClosed_singleton.preimage (continuous_apply i)

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem isOpen_Yo_regular (R : RegChartDataA A) : IsOpen R.Yo := by
  refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
  obtain ⟨j, hj⟩ := R.cover x
  have hs : x ∈ (R.chart j).source := R.mid_subset_source j (R.inner_subset_mid j hj)
  exact ⟨(R.chart j).source ∩ R.chart j ⁻¹' (coordDiv (R.S j))ᶜ,
    fun y hy => (R.mem_Yo j y hy.1).2 hy.2,
    (R.chart j).isOpen_inter_preimage (isClosed_coordDiv _).isOpen_compl, hs,
    (R.mem_Yo j x hs).1 hx⟩

namespace RegChartData

def ofRegular [CompactSpace X] (R : RegChartDataA A) (om : LocPot X) (om_pot : IsPotential A om)
    (om_pos : IsPosPot A om) : RegChartData A where
  toRegCharts := RegCharts.ofPotentialCharts R.toPotentialCharts om om_pot om_pos
  Yo := R.Yo
  isOpen_Yo := isOpen_Yo_regular R
  S := R.S
  mem_Yo_iff j z hz := by
    have h := R.mem_Yo j _ ((R.chart j).map_target hz)
    rwa [(R.chart j).right_inv hz] at h
  r := R.r
  f := R.f
  f_cont j := (R.f_smooth j).continuousOn
  f_bdd j := ⟨R.f_bdd.choose, R.f_bdd.choose_spec j⟩
  r_chart j z hz := by
    refine (R.r_chart j z hz).trans ?_
    simp only [Real.log_inv, Finset.sum_neg_distrib]
    ring
  one_le_r := R.one_le_r
  φ := R.ph
  φ_smooth := R.ph_smooth
  psh := R.u_psh
  C := |R.Clog| + |R.Cph| + |R.Cgrad|
  φ_le x hx := (R.ph_le x hx).trans
    (by linarith [le_abs_self R.Cph, abs_nonneg R.Clog, abs_nonneg R.Cgrad])
  le_φ x hx := by
    have h1 := R.ph_ge x hx
    have h2 : 0 ≤ Real.log (R.r x) := Real.log_nonneg (R.one_le_r x hx)
    have h3 : R.Clog ≤ |R.Clog| + |R.Cph| + |R.Cgrad| := by
      linarith [le_abs_self R.Clog, abs_nonneg R.Cph, abs_nonneg R.Cgrad]
    nlinarith
  grad j z hz := by
    have hYo : (R.chart j).symm z ∈ R.Yo :=
      (R.mem_Yo j _ ((R.chart j).map_target hz.1)).2 (by rw [(R.chart j).right_inv hz.1]; exact hz.2)
    have hr : 1 ≤ R.r ((R.chart j).symm z) := R.one_le_r _ hYo
    have hC0 : 0 ≤ |R.Clog| + |R.Cph| + |R.Cgrad| := by positivity
    have hCg : |R.Cgrad| ≤ |R.Clog| + |R.Cph| + |R.Cgrad| := by
      linarith [abs_nonneg R.Clog, abs_nonneg R.Cph]
    have hpos : 0 ≤ R.r ((R.chart j).symm z) ^ R.Cgrad := Real.rpow_nonneg (by linarith) _
    have h1 : R.Cgrad * R.r ((R.chart j).symm z) ^ R.Cgrad ≤
        (|R.Clog| + |R.Cph| + |R.Cgrad|) * R.r ((R.chart j).symm z) ^ (|R.Clog| + |R.Cph| + |R.Cgrad|) :=
      calc R.Cgrad * R.r ((R.chart j).symm z) ^ R.Cgrad
          ≤ (|R.Clog| + |R.Cph| + |R.Cgrad|) * R.r ((R.chart j).symm z) ^ R.Cgrad :=
            mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCg) hpos
        _ ≤ _ := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hr ((le_abs_self _).trans hCg)) hC0
    exact (R.grad_le j z hz).trans (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le)

def toRegular [T2Space X] (R : RegChartData A) (hW : ∀ j, R.W j ⊆ ball 0 1)
    (hf : ∀ j, ContDiffOn ℝ ∞ (R.f j) (R.W j)) : RegChartDataA A where
  toPotentialCharts := R.toRegCharts.toPotentialCharts hW
  S := R.S
  Yo := R.Yo
  mem_Yo j x hx := by
    have h := R.mem_Yo_iff j (R.ψ j x) hx.2
    rw [(R.ψ j).left_inv hx.1] at h
    exact h
  ph := R.φ
  ph_smooth := R.φ_smooth
  u_psh j := by
    have h := R.psh j
    rw [← R.toRegCharts.restrChart_target j] at h
    exact h
  r := R.r
  one_le_r := R.one_le_r
  f := R.f
  f_smooth j := (hf j).mono inter_subset_right
  f_bdd := by
    choose B hB using R.f_bdd
    exact ⟨∑ j, |B j|, fun j y hy => (hB j y hy.2).trans ((le_abs_self _).trans
      (Finset.single_le_sum (fun i _ => abs_nonneg (B i)) (Finset.mem_univ j)))⟩
  r_chart j y hy := by
    refine (R.r_chart j y ⟨hy.1.2, hy.2⟩).trans ?_
    simp only [Real.log_inv, Finset.sum_neg_distrib]
    ring
  Clog := R.C
  Cph := R.C
  ph_le := R.φ_le
  ph_ge x hx := by
    rw [neg_mul]
    exact R.le_φ x hx
  Cgrad := R.C
  grad_le j y hy := R.grad j y ⟨hy.1.2, hy.2⟩

end RegChartData

namespace BoundedThPsh

def ofBoundedPsh [CompactSpace X] (P : BoundedPshData A) (om : LocPot X) (om_pot : IsPotential A om)
    (om_pos : IsPosPot A om) :
    BoundedThPsh (RegCharts.ofPotentialCharts P.toPotentialCharts om om_pot om_pos) where
  φ := P.ph
  bdd := P.bdd
  psh := P.u_psh

def toBoundedPsh [T2Space X] {R : RegCharts A} (P : BoundedThPsh R) (hW : ∀ j, R.W j ⊆ ball 0 1) :
    BoundedPshData A where
  toPotentialCharts := R.toPotentialCharts hW
  ph := P.φ
  bdd := P.bdd
  u_psh j := by
    have h := P.psh j
    rw [← R.restrChart_target j] at h
    exact h

theorem ofBoundedPsh_φ [CompactSpace X] (P : BoundedPshData A) (om : LocPot X)
    (om_pot : IsPotential A om) (om_pos : IsPosPot A om) :
    (ofBoundedPsh P om om_pot om_pos).φ = P.ph := rfl

theorem toBoundedPsh_ph [T2Space X] {R : RegCharts A} (P : BoundedThPsh R)
    (hW : ∀ j, R.W j ⊆ ball 0 1) : (P.toBoundedPsh hW).ph = P.φ := rfl

end BoundedThPsh

theorem smoothed_eq_molli (R : RegChartDataA A) (ρ : Mollifier D) (K t : ℝ) (j : Fin R.N)
    (z : Fin D → ℂ) (ht : 0 < t) (hK : ∀ y ∈ ball z t, y ∉ coordDiv (R.S j) → -K ≤ R.u j y) :
    R.smoothed ρ K t j z = molli ρ t (R.u j) z := by
  unfold GroundTheory.Heights₂.Heights.Regular.RegChartData.smoothed molli
  have hae : ∀ᵐ w : Fin D → ℂ, ∀ i ∈ R.S j, w i ≠ z i := by
    rw [Filter.eventually_all_finset]
    intro i _
    rw [ae_iff]
    simp only [ne_eq, not_not]
    exact Measure.pi_eval_preimage_null (fun _ : Fin D => (volume : Measure ℂ)) (measure_singleton (z i))
  refine integral_congr_ae (hae.mono fun w hw => ?_)
  by_cases hρ : ρ.scaled t w = 0
  · simp [hρ]
  have hw1 : ‖w‖ < t := by
    have hs : t⁻¹ • w ∈ ball (0 : Fin D → ℂ) 1 :=
      ρ.support_subset fun h0 => hρ (by simp [Mollifier.scaled, h0])
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht] at hs
    rwa [inv_mul_lt_iff₀ ht, mul_one] at hs
  have hb : z - w ∈ ball z t := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
    exact hw1
  have hd : z - w ∉ coordDiv (R.S j) := by
    rintro ⟨i, hi, h0⟩
    exact hw i hi (by rw [Pi.sub_apply, sub_eq_zero] at h0; exact h0.symm)
  simp only [GroundTheory.Heights₂.Heights.Regular.RegChartData.trunc, limsupExt, if_neg hd]
  rw [max_eq_left (hK _ hb hd)]

theorem phReg_eq_phChart [CompactSpace X] (R : RegChartDataA A) (om : LocPot X)
    (om_pot : IsPotential A om) (om_pos : IsPosPot A om) (ρ : Mollifier D) (K t : ℝ) (j : Fin R.N)
    (x : X) (ht : 0 < t)
    (hK : ∀ y ∈ ball (R.chart j x) t, y ∉ coordDiv (R.S j) → -K ≤ R.u j y) :
    R.phReg ρ K t j x = (RegChartData.ofRegular R om om_pot om_pos).phChart R.ph ρ t j x := by
  unfold GroundTheory.Heights₂.Heights.Regular.RegChartData.phReg
  rw [smoothed_eq_molli R ρ K t j _ ht hK]
  rfl

theorem phChart_eq_phReg [T2Space X] (R : RegChartData A) (hW : ∀ j, R.W j ⊆ ball 0 1)
    (hf : ∀ j, ContDiffOn ℝ ∞ (R.f j) (R.W j)) (ρ : Mollifier D) (K t : ℝ) (j : Fin R.n) (x : X)
    (ht : 0 < t) (hK : ∀ y ∈ ball (R.ψ j x) t, y ∉ coordDiv (R.S j) → -K ≤ R.u R.φ j y) :
    (R.toRegular hW hf).phReg ρ K t j x = R.phChart R.φ ρ t j x := by
  unfold GroundTheory.Heights₂.Heights.Regular.RegChartData.phReg
  exact congrArg (fun s => s - R.q j (R.ψ j x)) (smoothed_eq_molli (R.toRegular hW hf) ρ K t j (R.ψ j x) ht hK)

theorem regularised_eq_glued [CompactSpace X] (R : RegChartDataA A) (om : LocPot X)
    (om_pot : IsPotential A om) (om_pos : IsPosPot A om) (ρ : Mollifier D) (K : ℝ)
    (η : Fin R.N → X → ℝ) (C t : ℝ) (x : X) (hε : 0 ≤ errorWithLinear C t)
    (hmol : ∀ j, x ∈ R.mid j →
      R.phReg ρ K t j x = (RegChartData.ofRegular R om om_pot om_pos).phChart R.ph ρ t j x) :
    R.regularised ρ K t (errorWithLinear C t) η x =
      (RegChartData.ofRegular R om om_pot om_pos).glued R.ph ρ η C t x := by
  set R' := RegChartData.ofRegular R om om_pot om_pos
  have hV : ∀ j, R'.toRegCharts.V' j = R.mid j :=
    RegCharts.ofPotentialCharts_V' R.toPotentialCharts om om_pot om_pos
  obtain ⟨hc1, hc2⟩ := (R'.cover x).choose_spec
  have hc : x ∈ R.mid (R'.cover x).choose := by
    rw [← hV]
    exact ⟨hc1, subset_closure.trans (R'.closure_W''_subset _) hc2⟩
  rw [GroundTheory.Heights₂.Heights.Regular.RegChartData.regularised, PotentialCharts.glue_eq_pad _ _ hε x hc]
  unfold RegCharts.glued RegCharts.regArg
  congr 2
  funext j
  split_ifs with h1 h2 h2
  · rw [hmol j h1]
  · exact absurd ((hV j).symm ▸ h1) h2
  · exact absurd ((hV j) ▸ h2) h1
  · rw [hmol _ hc]

theorem glued_eq_regularised [T2Space X] (R : RegChartData A) (hW : ∀ j, R.W j ⊆ ball 0 1)
    (hf : ∀ j, ContDiffOn ℝ ∞ (R.f j) (R.W j)) (ρ : Mollifier D) (K : ℝ) (η : Fin R.n → X → ℝ)
    (C t : ℝ) (x : X) (hε : 0 ≤ errorWithLinear C t)
    (hmol : ∀ j, x ∈ R.V' j → (R.toRegular hW hf).phReg ρ K t j x = R.phChart R.φ ρ t j x) :
    R.glued R.φ ρ η C t x = (R.toRegular hW hf).regularised ρ K t (errorWithLinear C t) η x := by
  obtain ⟨hc1, hc2⟩ := (R.cover x).choose_spec
  have hc : x ∈ (R.toRegular hW hf).mid (R.cover x).choose :=
    ⟨hc1, subset_closure.trans (R.closure_W''_subset _) hc2⟩
  unfold GroundTheory.Heights₂.Heights.Regular.RegChartData.regularised
  rw [PotentialCharts.glue_eq_pad _ _ hε x hc]
  unfold RegCharts.glued RegCharts.regArg
  congr 2
  funext j
  split_ifs with h1 h2 h2
  · rw [hmol j h1]
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rw [hmol _ hc]

theorem projLineCharts_not_subset_ball : ¬ ∀ j, projLineCharts.W j ⊆ ball 0 1 := by
  intro h
  have h1 : (fun _ : Fin 1 => (1 : ℂ)) ∈ projLineCharts.W 0 := by
    show _ ∈ ball (0 : Fin 1 → ℂ) 2
    rw [mem_ball_zero_iff, pi_norm_const]
    norm_num
  have h2 := h 0 h1
  rw [mem_ball_zero_iff, pi_norm_const] at h2
  norm_num at h2

theorem molli_fin_zero (ρ : Mollifier 0) (t : ℝ) (f : (Fin 0 → ℂ) → ℝ) (z : Fin 0 → ℂ) :
    molli ρ t f z = f z := by
  have h : ∀ w : Fin 0 → ℂ, ρ.scaled t w * f (z - w) = ρ.toFun w * f z := by
    intro w
    rw [Subsingleton.elim (z - w) z]
    simp only [Mollifier.scaled, mul_zero, pow_zero, inv_one, one_mul]
    rw [Subsingleton.elim (t⁻¹ • w) w]
  unfold molli
  simp_rw [h]
  rw [integral_mul_const, ρ.integral_eq_one, one_mul]

def pointOm : LocPot Unit := LocPot.ofFun fun _ => 0

theorem pointOm_pot : IsPotential pointAtlas pointOm :=
  ReciprocityTheory.AnForm.M.isPotential_ofFun _ _ fun _ => contDiffOn_const

theorem pointOm_pos : IsPosPot pointAtlas pointOm :=
  fun _ _ _ _ w hw => absurd (Subsingleton.elim w 0) hw

theorem phReg_ne_phChart_point (ρ : Mollifier 0) (t : ℝ) :
    pointReg.phReg ρ (-1) t (0 : Fin 1) () = 1 ∧
      (RegChartData.ofRegular pointReg pointOm pointOm_pot pointOm_pos).phChart pointReg.ph ρ t (0 : Fin 1) () = 0 := by
  constructor
  · simp [GroundTheory.Heights₂.Heights.Regular.RegChartData.phReg,
      GroundTheory.Heights₂.Heights.Regular.RegChartData.smoothed, molli_fin_zero,
      GroundTheory.Heights₂.Heights.Regular.RegChartData.trunc, limsupExt, coordDiv,
      GroundTheory.Heights₂.Heights.Regular.RegChartData.u, PotentialCharts.chartFun, pointReg, pointCharts]
  · simp [RegCharts.phChart, molli_fin_zero, RegCharts.u, RegChartData.ofRegular,
      RegCharts.ofPotentialCharts, pointReg, pointCharts]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
