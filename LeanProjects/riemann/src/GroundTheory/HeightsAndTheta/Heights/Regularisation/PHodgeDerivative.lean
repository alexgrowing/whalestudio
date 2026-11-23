import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsBounds
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Matrix
open GroundTheory.Heights₂.Heights.MCBounds GroundTheory.Heights₂.Heights.MCDet
open scoped ComplexOrder

noncomputable section

namespace HodgeDerivative

theorem norm_coord_lt {n : ℕ} {z : Fin n → ℂ} (hz : z ∈ ball (0 : Fin n → ℂ) 1) (k : Fin n) :
    ‖z k‖ < 1 :=
  (norm_le_pi_norm z k).trans_lt (mem_ball_zero_iff.mp hz)

theorem isOpen_punctured {n a : ℕ} (h : a ≤ n) :
    IsOpen (puncturedChart h (ball (0 : Fin n → ℂ) 1)) := by
  have e : puncturedChart h (ball (0 : Fin n → ℂ) 1) =
      ball 0 1 ∩ ⋂ j : Fin a, {z : Fin n → ℂ | z (Fin.castLE h j) ≠ 0} := by
    ext z
    simp [puncturedChart, cuspCoord]
  rw [e]
  exact isOpen_ball.inter
    (isOpen_iInter_of_finite fun j => isOpen_ne_fun (continuous_apply _) continuous_const)

theorem logLift_mem {n a : ℕ} (h : a ≤ n) {z : Fin n → ℂ}
    (hz : z ∈ puncturedChart h (ball (0 : Fin n → ℂ) 1)) : logLift a z ∈ logCover h := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · have hi : (Fin.castLE h i).val < a := i.isLt
    have h0 : z (Fin.castLE h i) ≠ 0 := hz.2 i
    simp only [logLift, if_pos hi, Complex.log_re]
    exact Real.log_neg (norm_pos_iff.mpr h0) (norm_coord_lt hz.1 _)
  · simp only [logLift, if_neg (not_lt.mpr hk)]
    exact norm_coord_lt hz.1 k

theorem expCover_logLift {n a : ℕ} (h : a ≤ n) {z : Fin n → ℂ} (hz : ∀ j, cuspCoord h z j ≠ 0) :
    expCover a (logLift a z) = z := by
  funext k
  by_cases hk : k.val < a
  · have e : Fin.castLE h ⟨k.val, hk⟩ = k := Fin.ext rfl
    have h0 : z k ≠ 0 := by
      have := hz ⟨k.val, hk⟩
      rwa [cuspCoord, e] at this
    simp only [expCover, logLift, if_pos hk, Complex.exp_log h0]
  · simp only [expCover, logLift, if_neg hk]

theorem imTau_eq {n a g : ℕ} (P : PeriodPolydisc n a g) {T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    (hT : P.IsTau0Ext T0) {z : Fin n → ℂ} (hz : z ∈ puncturedChart P.a_le (ball (0 : Fin n → ℂ) 1)) :
    P.imTau z = chartImag P.a_le T0 (fun i => (P.B i).map (Int.cast : ℤ → ℝ)) z := by
  have hw := logLift_mem P.a_le hz
  have h0 : P.tau0 (logLift a z) = T0 z := by
    rw [hT.2 _ hw, expCover_logLift P.a_le hz.2]
  have hτ : P.τ (logLift a z) = T0 z + ∑ i : Fin a,
      (logLift a z (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I)) •
        (P.B i).map (Int.cast : ℤ → ℂ) := by
    rw [← h0, PeriodPolydisc.tau0, sub_add_cancel]
  ext p q
  simp only [PeriodPolydisc.imTau, hτ, chartImag, map_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Complex.add_im, Complex.im_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (Fin.castLE P.a_le i).val < a := i.isLt
  simp only [logLift, if_pos hi, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, mul_zero,
    zero_add, im_div_two_pi_I, Complex.log_re, cuspTime, cuspCoord, Real.log_inv]
  ring

theorem logNorm_hasFDerivAt {x : ℂ} (hx : x ≠ 0) :
    ∃ L : ℂ →L[ℝ] ℝ, HasFDerivAt (fun y : ℂ => Real.log ‖y‖) L x ∧ ‖L‖ ≤ ‖x‖⁻¹ := by
  have hx2 : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have h1 := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.log hx2).const_mul (2⁻¹ : ℝ)
  have e : (fun y : ℂ => 2⁻¹ * Real.log (‖y‖ ^ 2)) = fun y : ℂ => Real.log ‖y‖ := by
    funext y
    rw [Real.log_pow]
    push_cast
    ring
  rw [e] at h1
  refine ⟨_, h1, ?_⟩
  rw [two_nsmul, ← two_smul ℝ]
  rw [norm_smul, norm_smul, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), abs_of_pos (by norm_num : (0:ℝ) < 2),
    abs_of_pos (inv_pos.mpr (by positivity))]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  apply le_of_eq
  field_simp

theorem cuspTime_hasFDerivAt {n a : ℕ} (h : a ≤ n) (i : Fin a) {z : Fin n → ℂ}
    (hz : cuspCoord h z i ≠ 0) :
    ∃ L : (Fin n → ℂ) →L[ℝ] ℝ, HasFDerivAt (fun y => cuspTime h y i) L z ∧
      ‖L‖ ≤ ‖cuspCoord h z i‖⁻¹ := by
  obtain ⟨L, hL, hLn⟩ := logNorm_hasFDerivAt hz
  have hp : HasFDerivAt (fun y : Fin n → ℂ => y (Fin.castLE h i))
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) (Fin.castLE h i)) z :=
    hasFDerivAt_apply _ _
  have h2 := (hL.comp z hp).const_mul (-(2 * Real.pi)⁻¹)
  have e : (fun y : Fin n → ℂ => -(2 * Real.pi)⁻¹ * (Real.log ‖y (Fin.castLE h i)‖)) =
      fun y => cuspTime h y i := by
    funext y
    simp only [cuspTime, cuspCoord, Real.log_inv]
    ring
  rw [Function.comp_def, e] at h2
  refine ⟨_, h2, ?_⟩
  have hproj : ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) (Fin.castLE h i)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      simpa using norm_le_pi_norm v (Fin.castLE h i)
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hc : ‖(-(2 * Real.pi)⁻¹ : ℝ)‖ ≤ 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ hpi
  calc ‖(-(2 * Real.pi)⁻¹ : ℝ) • L.comp _‖
      ≤ ‖(-(2 * Real.pi)⁻¹ : ℝ)‖ * (‖L‖ * 1) := by
        rw [norm_smul]
        gcongr
        exact (L.opNorm_comp_le _).trans (by gcongr)
    _ ≤ 1 * (‖cuspCoord h z i‖⁻¹ * 1) := by gcongr
    _ = ‖cuspCoord h z i‖⁻¹ := by ring

theorem im_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (fun y => (f y).im) (Complex.imCLM.comp (fderiv ℝ f x)) x ∧
      ‖Complex.imCLM.comp (fderiv ℝ f x)‖ ≤ ‖fderiv ℝ f x‖ := by
  refine ⟨Complex.imCLM.hasFDerivAt.comp x hf.hasFDerivAt, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  simp only [ContinuousLinearMap.comp_apply, Complex.imCLM_apply, Real.norm_eq_abs]
  exact (Complex.abs_im_le_norm _).trans ((fderiv ℝ f x).le_opNorm v)

theorem one_add_sum_le {n a : ℕ} (h : a ≤ n) {z : Fin n → ℂ}
    (hz : z ∈ puncturedChart h (ball (0 : Fin n → ℂ) 1)) :
    1 + ∑ i, ‖cuspCoord h z i‖⁻¹ ≤ (1 + a) * Real.exp (chartRadius h z / 2) := by
  have hlt : ∀ j, ‖cuspCoord h z j‖ < 1 := fun j => norm_coord_lt hz.1 _
  have hnn : ∀ j, 0 ≤ Real.log (‖cuspCoord h z j‖ ^ 2)⁻¹ := fun j => log_inv_sq_nonneg (hlt j)
  have hr0 : 0 ≤ chartRadius h z :=
    add_nonneg (Real.exp_pos 1).le (Finset.sum_nonneg fun j _ => hnn j)
  have h1 : 1 ≤ Real.exp (chartRadius h z / 2) := Real.one_le_exp (by linarith)
  have hi : ∀ i, ‖cuspCoord h z i‖⁻¹ ≤ Real.exp (chartRadius h z / 2) := by
    intro i
    have hpos : 0 < ‖cuspCoord h z i‖ := norm_pos_iff.mpr (hz.2 i)
    have e1 : Real.log (‖cuspCoord h z i‖ ^ 2)⁻¹ = 2 * Real.log ‖cuspCoord h z i‖⁻¹ := by
      rw [Real.log_inv, Real.log_inv, Real.log_pow]
      push_cast
      ring
    have hs := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    have hle : Real.log ‖cuspCoord h z i‖⁻¹ ≤ chartRadius h z / 2 := by
      unfold chartRadius
      rw [e1] at hs
      linarith [Real.exp_pos 1]
    calc ‖cuspCoord h z i‖⁻¹ = Real.exp (Real.log ‖cuspCoord h z i‖⁻¹) :=
          (Real.exp_log (inv_pos.mpr hpos)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hle
  have hs : ∑ i, ‖cuspCoord h z i‖⁻¹ ≤ a * Real.exp (chartRadius h z / 2) := by
    calc ∑ i, ‖cuspCoord h z i‖⁻¹ ≤ ∑ _i : Fin a, Real.exp (chartRadius h z / 2) :=
          Finset.sum_le_sum fun i _ => hi i
      _ = a * Real.exp (chartRadius h z / 2) := by simp
  linarith

theorem one_le_chartRadius {n a : ℕ} (h : a ≤ n) {z : Fin n → ℂ}
    (hz : z ∈ puncturedChart h (ball (0 : Fin n → ℂ) 1)) : 1 ≤ chartRadius h z := by
  have : 0 ≤ ∑ j, Real.log (‖cuspCoord h z j‖ ^ 2)⁻¹ :=
    Finset.sum_nonneg fun j _ => log_inv_sq_nonneg (norm_coord_lt hz.1 _)
  unfold chartRadius
  linarith [Real.add_one_le_exp (1 : ℝ)]

theorem chartImag_entry_deriv {n a g : ℕ} (h : a ≤ n) (T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (p q : Fin g) {z : Fin n → ℂ}
    (hz : ∀ j, cuspCoord h z j ≠ 0) (hT : DifferentiableAt ℝ (fun y => T0 y p q) z) :
    DifferentiableAt ℝ (fun y => chartImag h T0 B y p q) z ∧
      ‖fderiv ℝ (fun y => chartImag h T0 B y p q) z‖ ≤
        ‖fderiv ℝ (fun y => T0 y p q) z‖ + ∑ i, |B i p q| * ‖cuspCoord h z i‖⁻¹ := by
  have e : (fun y => chartImag h T0 B y p q) =
      fun y => (T0 y p q).im + ∑ i, cuspTime h y i * B i p q := by
    funext y
    simp [chartImag, Matrix.sum_apply]
  choose L hL hLn using fun i => cuspTime_hasFDerivAt h i (hz i)
  obtain ⟨h0, h0n⟩ := im_hasFDerivAt hT
  have hsum : HasFDerivAt (fun y => ∑ i, cuspTime h y i * B i p q) (∑ i, B i p q • L i) z :=
    (HasFDerivAt.sum (u := Finset.univ) (A := fun i y => cuspTime h y i * B i p q)
      fun i _ => (hL i).mul_const (B i p q)).congr_of_eventuallyEq
        (Eventually.of_forall fun y => by simp only [Finset.sum_apply])
  have hall : HasFDerivAt (fun y => (T0 y p q).im + ∑ i, cuspTime h y i * B i p q)
      (Complex.imCLM.comp (fderiv ℝ (fun y => T0 y p q) z) + ∑ i, B i p q • L i) z := h0.add hsum
  rw [e]
  refine ⟨hall.differentiableAt, ?_⟩
  rw [hall.fderiv]
  refine (norm_add_le _ _).trans (add_le_add h0n ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hLn i) (abs_nonneg _)

end HodgeDerivative

open HodgeDerivative in

theorem HodgeDerivative.proof (h0 : ImTauBounds.Statement) (h1 : Tau0Holomorphic.Statement)
    (hAn : AnalyticDerivBound.Statement) (hInv : InvEntryDeriv.Statement)
    (hLDG : LogDetGramDeriv.Statement) : HodgeDerivative.Statement := by
  intro n a g P
  obtain ⟨ρ, c, C, hρ0, hρ1, hc, hb⟩ := h0 n a g P
  obtain ⟨-, T0, hT⟩ := h1 n a g P
  set Bℝ : Fin a → Matrix (Fin g) (Fin g) ℝ := fun i => (P.B i).map (Int.cast : ℤ → ℝ) with hBℝ
  set Y : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℝ := chartImag P.a_le T0 Bℝ with hY
  have hKc : IsCompact (closedBall (0 : Fin n → ℂ) ρ) := isCompact_closedBall _ _
  have hKU : closedBall (0 : Fin n → ℂ) ρ ⊆ ball 0 1 := closedBall_subset_ball hρ1
  have hT0 := fun p q => hAn (fun y => T0 y p q) (ball 0 1) _ isOpen_ball (hT.1 p q) hKc hKU
  choose A hA0 hA using hT0
  set β : ℝ := ∑ i, ∑ p, ∑ q, |Bℝ i p q| with hβ
  set SA : ℝ := ∑ p, ∑ q, A p q with hSA
  set C0 : ℝ := SA + β with hC0
  have hAle : ∀ p q, A p q ≤ SA := fun p q =>
    (Finset.single_le_sum (f := fun q => A p q) (fun q _ => (hA0 p q).le) (Finset.mem_univ q)).trans
      (Finset.single_le_sum (f := fun p => ∑ q, A p q)
        (fun p _ => Finset.sum_nonneg fun q _ => (hA0 p q).le) (Finset.mem_univ p))
  have hBle : ∀ i p q, |Bℝ i p q| ≤ β := fun i p q =>
    ((Finset.single_le_sum (f := fun q => |Bℝ i p q|) (fun q _ => abs_nonneg _)
        (Finset.mem_univ q)).trans
      (Finset.single_le_sum (f := fun p => ∑ q, |Bℝ i p q|)
        (fun p _ => Finset.sum_nonneg fun q _ => abs_nonneg _) (Finset.mem_univ p))).trans
      (Finset.single_le_sum (f := fun i => ∑ p, ∑ q, |Bℝ i p q|)
        (fun i _ => Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => abs_nonneg _)
        (Finset.mem_univ i))
  have hβ0 : 0 ≤ β := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun p _ =>
    Finset.sum_nonneg fun q _ => abs_nonneg _
  have hSA0 : 0 ≤ SA := Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => (hA0 p q).le
  have hC00 : 0 ≤ C0 := add_nonneg hSA0 hβ0

  have hpt : ∀ z ∈ closedBall (0 : Fin n → ℂ) ρ, z ∈ puncturedChart P.a_le (ball 0 1) →
      (Y z - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef ∧
      ((max C 1 * chartRadius P.a_le z) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y z).PosSemidef ∧
      (∀ p q, DifferentiableAt ℝ (fun y => Y y p q) z ∧
        ‖fderiv ℝ (fun y => Y y p q) z‖ ≤ C0 * (1 + ∑ i, ‖cuspCoord P.a_le z i‖⁻¹)) ∧
      (∀ p q, (fun y => P.hodge y p q) =ᶠ[𝓝 z] fun y => (Y y)⁻¹ p q) ∧
      (∀ (k : ℕ) (F : (Fin n → ℂ) → Matrix (Fin g) (Fin k) ℂ),
        (fun y => logDetGram (P.imTau y) (F y)) =ᶠ[𝓝 z] fun y => logDetGram (Y y) (F y)) := by
    intro z hzρ hz
    have hw := logLift_mem P.a_le hz
    have hexp := expCover_logLift P.a_le hz.2
    obtain ⟨hlow, hup⟩ := hb _ hw (by rw [hexp]; exact hzρ)
    have hIm : (P.τ (logLift a z)).map Complex.im = Y z := imTau_eq P hT hz
    rw [hIm] at hlow hup
    rw [hexp] at hup
    have hr1 := one_le_chartRadius P.a_le hz
    have hEq : ∀ᶠ y in 𝓝 z, P.imTau y = Y y :=
      Filter.eventually_of_mem ((isOpen_punctured P.a_le).mem_nhds hz) fun y hy => imTau_eq P hT hy
    refine ⟨hlow, ?_, fun p q => ?_, fun p q => hEq.mono fun y hy => ?_,
      fun k F => hEq.mono fun y hy => ?_⟩
    · have e : (max C 1 * chartRadius P.a_le z) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y z =
          ((C * chartRadius P.a_le z) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y z) +
            ((max C 1 - C) * chartRadius P.a_le z) • (1 : Matrix (Fin g) (Fin g) ℝ) := by
        rw [sub_mul, sub_smul]; abel
      rw [e]
      exact hup.add (PosSemidef.one.smul
        (mul_nonneg (sub_nonneg.mpr (le_max_left _ _)) (by linarith)))
    · obtain ⟨hd, hn⟩ := chartImag_entry_deriv P.a_le T0 Bℝ p q hz.2 (hA p q z hzρ).1
      refine ⟨hd, hn.trans ?_⟩
      have hS0 : 0 ≤ ∑ i, ‖cuspCoord P.a_le z i‖⁻¹ :=
        Finset.sum_nonneg fun i _ => inv_nonneg.mpr (norm_nonneg _)
      have h2 : ∑ i, |Bℝ i p q| * ‖cuspCoord P.a_le z i‖⁻¹ ≤
          β * ∑ i, ‖cuspCoord P.a_le z i‖⁻¹ := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hBle i p q) (inv_nonneg.mpr (norm_nonneg _))
      have h3 := (hA p q z hzρ).2.2
      have h4 := hAle p q
      nlinarith
    · simp only [PeriodPolydisc.hodge, hy]
    · simp only [hy]
  refine ⟨ρ, hρ0, hρ1, ⟨(g : ℝ) ^ 2 * c⁻¹ ^ 2 * C0 * (1 + a), fun z hzρ hz p q => ?_⟩, ?_⟩
  · obtain ⟨hYc, -, hYd, hH, -⟩ := hpt z hzρ hz
    have hi := hInv g Y z c _ hc hYc hYd p q
    rw [(hH p q).differentiableAt_iff, (hH p q).fderiv_eq]
    have hS0 : 0 ≤ ∑ i, ‖cuspCoord P.a_le z i‖⁻¹ :=
      Finset.sum_nonneg fun i _ => inv_nonneg.mpr (norm_nonneg _)
    have hk0 : 0 ≤ (g : ℝ) ^ 2 * c⁻¹ ^ 2 * C0 := by positivity
    have ha1 : (1 : ℝ) ≤ 1 + a := by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
    refine ⟨hi.1, hi.2.trans ?_, hi.2.trans ?_⟩
    · rw [← mul_assoc, mul_assoc _ (1 + (a : ℝ))]
      exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith) ha1) hk0
    · have := one_add_sum_le P.a_le hz
      rw [← mul_assoc, mul_assoc _ (1 + (a : ℝ))]
      exact mul_le_mul_of_nonneg_left this hk0
  · intro k F hF hrank
    obtain ⟨Kc, hKc0, hKmain⟩ := hLDG g k
    have hFb := fun j l => hAn (fun y => F y j l) (ball 0 1) _ isOpen_ball (hF j l) hKc hKU
    choose AF hAF0 hAF using hFb
    set aF : ℝ := ∑ j, ∑ l, AF j l with haF
    have hAFle : ∀ j l, AF j l ≤ aF := fun j l =>
      (Finset.single_le_sum (f := fun l => AF j l) (fun l _ => (hAF0 j l).le)
        (Finset.mem_univ l)).trans
        (Finset.single_le_sum (f := fun j => ∑ l, AF j l)
          (fun j _ => Finset.sum_nonneg fun l _ => (hAF0 j l).le) (Finset.mem_univ j))
    have haF0 : 0 ≤ aF := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => (hAF0 j l).le
    obtain ⟨δ, hδ, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧
        ∀ z ∈ closedBall (0 : Fin n → ℂ) ρ, δ ≤ ((F z)ᴴ * F z).det.re := by
      have hcont : ContinuousOn F (closedBall 0 ρ) := by
        rw [continuousOn_iff_continuous_domRestrict]
        exact continuous_matrix fun j l => ((hF j l).continuousOn.mono hKU).domRestrict
      have hc' : ContinuousOn (fun y => ((F y)ᴴ * F y).det.re) (closedBall 0 ρ) := by
        rw [continuousOn_iff_continuous_domRestrict] at hcont ⊢
        exact Complex.continuous_re.comp (hcont.matrix_conjTranspose.matrix_mul hcont).matrix_det
      obtain ⟨z0, hz0, hmin⟩ := hKc.exists_isMinOn ⟨0, mem_closedBall_self hρ0.le⟩ hc'
      exact ⟨_, re_det_pos (gram_posDef _ (hrank z0 (hKU hz0))), fun z hz => hmin hz⟩
    set C1 : ℝ := max C 1 with hC1def
    have hC1 : 0 < C1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    set W : ℝ := Kc * (1 + aF) ^ (2 * k) * (1 + c⁻¹) ^ (k + 1) * C1 ^ k / δ with hW
    have hW0 : 0 ≤ W := by positivity
    set Q : ℝ := W * (1 + C0) with hQ
    have hQ0 : 0 ≤ Q := by positivity
    have ha1 : (1 : ℝ) ≤ 1 + a := by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
    refine ⟨max (Q * (1 + a)) k, fun z hzρ hz => ?_⟩
    obtain ⟨hYc, hYup, hYd, -, hL⟩ := hpt z hzρ hz
    have hr1 := one_le_chartRadius P.a_le hz
    set r := chartRadius P.a_le z with hr
    set S := ∑ i, ‖cuspCoord P.a_le z i‖⁻¹ with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => inv_nonneg.mpr (norm_nonneg _)
    have hYpd := posDef_of_ge hc hYc
    have hl : 0 < C1 * r := by positivity
    have hμle : (C1 * r)⁻¹ ^ k * δ ≤
        ((F z)ᴴ * (Y z)⁻¹.map (fun x : ℝ => (x : ℂ)) * F z).det.re := by
      have h1 := posSemidef_map_ofReal (inv_ge_of_le hl hYpd hYup)
      rw [map_sub_smul_one] at h1
      have h2 := h1.conjTranspose_mul_mul_same (F z)
      rw [conj_sub_smul_one] at h2
      have h3 : ((((C1 * r)⁻¹ : ℝ) : ℂ) • ((F z)ᴴ * F z)).PosSemidef :=
        (posSemidef_conjTranspose_mul_self (F z)).smul
          (Complex.zero_le_real.mpr (inv_nonneg.mpr hl.le))
      have := re_det_mono h3 h2
      simp only [RCLike.re_to_complex] at this
      rw [re_det_ofReal_smul] at this
      exact le_trans (mul_le_mul_of_nonneg_left (hδle z hzρ) (by positivity)) this
    have hFent : ∀ j l, DifferentiableAt ℝ (fun y => F y j l) z ∧ ‖F z j l‖ ≤ aF ∧
        ‖fderiv ℝ (fun y => F y j l) z‖ ≤ aF := fun j l =>
      ⟨(hAF j l z hzρ).1, (hAF j l z hzρ).2.1.trans (hAFle j l),
        (hAF j l z hzρ).2.2.trans (hAFle j l)⟩
    have hm := hKmain F Y z aF (C0 * (1 + S)) c ((C1 * r)⁻¹ ^ k * δ) hc (by positivity) haF0
      (by positivity) hFent hYd hYc hμle
    rw [(hL k F).differentiableAt_iff, (hL k F).fderiv_eq]

    have hX : Kc * (1 + aF) ^ (2 * k) * (1 + c⁻¹) ^ (k + 1) * (1 + C0 * (1 + S)) /
        ((C1 * r)⁻¹ ^ k * δ) ≤ Q * r ^ k * (1 + S) := by
      have e : Kc * (1 + aF) ^ (2 * k) * (1 + c⁻¹) ^ (k + 1) * (1 + C0 * (1 + S)) /
          ((C1 * r)⁻¹ ^ k * δ) = W * r ^ k * (1 + C0 * (1 + S)) := by
        rw [hW, inv_pow, mul_pow]
        field_simp
      rw [e, hQ, mul_assoc W (1 + C0), mul_comm (1 + C0), ← mul_assoc W, mul_assoc (W * r ^ k)]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have hCf : Q * (1 + a) ≤ max (Q * (1 + a)) k := le_max_left _ _
    have hQf : Q ≤ max (Q * (1 + a)) k := (le_mul_of_one_le_right hQ0 ha1).trans hCf
    have hrk : r ^ k ≤ r ^ (max (Q * (1 + a)) k) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hr1 (le_max_right _ _)
    have hrk0 : 0 ≤ r ^ k := by positivity
    refine ⟨hm.1, hm.2.trans (hX.trans ?_), hm.2.trans (hX.trans ?_)⟩
    · exact mul_le_mul_of_nonneg_right (mul_le_mul hQf hrk hrk0 (by linarith)) (by linarith)
    · have hE := one_add_sum_le P.a_le hz
      calc Q * r ^ k * (1 + S) ≤ Q * r ^ k * ((1 + a) * Real.exp (r / 2)) :=
            mul_le_mul_of_nonneg_left hE (by positivity)
        _ = Q * (1 + a) * r ^ k * Real.exp (r / 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul hCf hrk hrk0 (by linarith)) (Real.exp_pos _).le

end

end GroundTheory.Heights₂.Heights.Regular
