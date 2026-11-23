import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSectionSmoothPolydiscStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothBoundedGradientOnHalfBallStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSqGradientIdentityStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff

namespace GlobalTheory.CompBounds

theorem sq_add_le (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

theorem sq_add_ge (x y δ : ℝ) (h0 : 0 < δ) (h1 : δ ≤ 1 / 2) :
    δ * x ^ 2 - 2 * δ * y ^ 2 ≤ (x + y) ^ 2 := by
  have h1' : 0 < 1 - δ := by linarith
  have key : 0 ≤ (1 - δ) * ((x + y) ^ 2 - (δ * x ^ 2 - 2 * δ * y ^ 2)) := by
    nlinarith [sq_nonneg ((1 - δ) * x + y), mul_nonneg h0.le (by linarith : (0:ℝ) ≤ 1 - 2 * δ), sq_nonneg y]
  have := (mul_nonneg_iff_of_pos_left h1').1 key
  linarith

theorem core {a b u₁ u₂ P t r S Cf C : ℝ} (hab : a ^ 2 + b ^ 2 = 4 * P * t ^ 2) (hP : 0 ≤ P)
    (hu : u₁ ^ 2 + u₂ ^ 2 ≤ Cf * S) (hS : 0 ≤ S) (hCf : 0 ≤ Cf) (hCfC : Cf ≤ C) (ht : 0 < t)
    (hr₁ : 2 * Real.pi * t ≤ r) (hr₂ : r ≤ 6 * Real.pi * t) (hr₃ : 1 ≤ r) :
    1 / Real.pi * (((-a + u₁) ^ 2 + (-b + u₂) ^ 2) / 4) / r ^ 2 ≤ P + C * S ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      δ * P / (36 * Real.pi ^ 3) - δ * C * S ≤ 1 / Real.pi * (((-a + u₁) ^ 2 + (-b + u₂) ^ 2) / 4) / r ^ 2 := by
  have hπ := Real.pi_gt_three
  have hπ0 := Real.pi_pos
  have hr0 : 0 < r := by nlinarith
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have hrt : 4 * Real.pi ^ 2 * t ^ 2 ≤ r ^ 2 := by nlinarith
  have hrt' : r ^ 2 ≤ 36 * Real.pi ^ 2 * t ^ 2 := by nlinarith
  have hCS : Cf * S ≤ C * S := mul_le_mul_of_nonneg_right hCfC hS
  have hCfS : 0 ≤ Cf * S := mul_nonneg hCf hS
  have eq : ∀ G : ℝ, 1 / Real.pi * (G / 4) / r ^ 2 = G / (4 * Real.pi * r ^ 2) := by
    intro G; field_simp; try ring
  rw [eq]
  have hden : 0 < 4 * Real.pi * r ^ 2 := by positivity
  constructor
  · rw [div_le_iff₀ hden]
    have h1 := sq_add_le (-a) u₁
    have h2 := sq_add_le (-b) u₂
    have hπ3 : 1 ≤ Real.pi ^ 3 := by nlinarith
    have A1 : 8 * P * t ^ 2 ≤ 4 * Real.pi * r ^ 2 * P := by
      have : 16 * Real.pi ^ 3 * t ^ 2 ≤ 4 * Real.pi * r ^ 2 := by nlinarith
      nlinarith [mul_nonneg hP (sq_nonneg t)]
    have A2 : 2 * (Cf * S) ≤ 4 * Real.pi * r ^ 2 * (C * S) := by
      have : (2:ℝ) ≤ 4 * Real.pi * r ^ 2 := by nlinarith
      nlinarith
    nlinarith
  · intro δ h0 h1
    rw [le_div_iff₀ hden]
    have g1 := sq_add_ge (-a) u₁ δ h0 h1
    have g2 := sq_add_ge (-b) u₂ δ h0 h1
    have hδP : 0 ≤ δ * P := mul_nonneg h0.le hP
    have B1 : δ * P / (36 * Real.pi ^ 3) * (4 * Real.pi * r ^ 2) ≤ 4 * δ * P * t ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hrt' (by positivity : (0:ℝ) ≤ δ * P * 4 * Real.pi)]
    have B2 : 2 * δ * (Cf * S) ≤ δ * C * S * (4 * Real.pi * r ^ 2) := by
      have : (2:ℝ) ≤ 4 * Real.pi * r ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hCS h0.le, mul_nonneg h0.le (mul_nonneg (le_trans hCfS hCS) (by linarith : (0:ℝ) ≤ 4 * Real.pi * r ^ 2 - 2))]
    have e1 : (-a) ^ 2 = a ^ 2 := by ring
    have e2 : (-b) ^ 2 = b ^ 2 := by ring
    rw [e1] at g1; rw [e2] at g2
    have hu' : 2 * δ * (u₁ ^ 2 + u₂ ^ 2) ≤ 2 * δ * (Cf * S) :=
      mul_le_mul_of_nonneg_left hu (by linarith)
    have hab' : δ * a ^ 2 + δ * b ^ 2 = 4 * δ * P * t ^ 2 := by rw [← mul_add, hab]; ring
    rw [sub_mul]
    linarith

theorem xt_bounds {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    0 < x * (-Real.log x / (2 * Real.pi)) ∧ x * (-Real.log x / (2 * Real.pi)) ≤ 1 := by
  have hl : Real.log x < 0 := Real.log_neg h0 h1
  have h2 := Real.one_sub_inv_le_log_of_pos h0
  have hπ := Real.pi_gt_three
  constructor
  · apply mul_pos h0; apply div_pos (by linarith); positivity
  · have : x * (-Real.log x) ≤ 1 := by
      have : x * x⁻¹ = 1 := mul_inv_cancel₀ h0.ne'
      nlinarith
    rw [mul_div_assoc']
    rw [div_le_one (by positivity)]
    nlinarith

end GlobalTheory.CompBounds

namespace GlobalTheory.CompBounds

theorem compBounds : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)), IsBoundary A L s D → IsAdaptedPolydisc A D ψ σ → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.ball (0 : Fin e → ℂ) ρ, ψ.symm z ∉ ⋃ i, D i → ∀ w : Fin e → ℂ, (∀ (i : Fin m) (k : Fin e), σ i = some k → ‖w k‖ ^ 2 ≤ ‖w k‖ ^ 2 / (‖z k‖ ^ 2 * tOf (z k) ^ 2)) ∧ ∀ i : Fin m, gradSqAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z) ^ 2 ≤ Option.elim (σ i) 0 (fun k => ‖w k‖ ^ 2 / (‖z k‖ ^ 2 * tOf (z k) ^ 2)) + C * ∑ k, ‖w k‖ ^ 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → δ * Option.elim (σ i) 0 (fun k => ‖w k‖ ^ 2 / (‖z k‖ ^ 2 * tOf (z k) ^ 2)) / (36 * Real.pi ^ 3) - δ * C * ∑ k, ‖w k‖ ^ 2 ≤ gradSqAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z) ^ 2 := by
  intro e X _ A m L s D ψ σ hB hP
  choose f hfs hfeq using GlobalTheory.T.normal_section_smooth_polydisc A L s D ψ σ hB hP
  choose Cf hCf0 hCf using fun i => GlobalTheory.T.smooth_bounded_gradient_on_half_ball (f i) (hfs i)
  set M := Real.exp 1 + ∑ i, Cf i with hM
  have hSum0 : 0 ≤ ∑ i, Cf i := Finset.sum_nonneg fun i _ => hCf0 i
  have hCfle : ∀ i, Cf i ≤ ∑ j, Cf j := fun i =>
    Finset.single_le_sum (fun j _ => hCf0 j) (Finset.mem_univ i)
  refine ⟨min (1 / 2) (Real.exp (-M)), lt_min (by norm_num) (Real.exp_pos _), min_le_left _ _,
    ∑ i, Cf i + 1, by linarith, ?_⟩
  intro z hz hzD w
  have hzρ : ‖z‖ < min (1 / 2) (Real.exp (-M)) := by simpa using hz
  have hz12 : ‖z‖ < 1 / 2 := lt_of_lt_of_le hzρ (min_le_left _ _)
  have hzM : ‖z‖ < Real.exp (-M) := lt_of_lt_of_le hzρ (min_le_right _ _)
  have hz1 : z ∈ Metric.ball (0 : Fin e → ℂ) 1 := by
    rw [mem_ball_zero_iff]; linarith
  have hzc : z ∈ Metric.closedBall (0 : Fin e → ℂ) (1 / 2) := by
    rw [mem_closedBall_zero_iff]; linarith
  have hne : ∀ i k, σ i = some k → z k ≠ 0 := by
    intro i k hk hzk
    exact hzD (Set.mem_iUnion.2 ⟨i, (hP.2.2.2 z hz1 i).2 ⟨k, hk, hzk⟩⟩)
  have hxk : ∀ k, ‖z k‖ ≤ ‖z‖ := fun k => norm_le_pi_norm z k
  have hS : 0 ≤ ∑ k, ‖w k‖ ^ 2 := by positivity
  have hre : ∀ i, Real.exp 1 ≤ rComp L s i (ψ.symm z) := by
    intro i
    have h1 := (hB i).2.2.2 (ψ.symm z)
    have h0 : 0 ≤ normSec (L i) (s i) (ψ.symm z) := by unfold normSec; positivity
    have : Real.log (normSec (L i) (s i) (ψ.symm z) ^ 2) ≤ 0 :=
      Real.log_nonpos (by positivity) (pow_le_one₀ h0 h1)
    unfold rComp; linarith
  have he1 : (1:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
  have hfd : ∀ i, DifferentiableAt ℝ (f i) z := fun i =>
    ((hfs i).differentiableOn (by simp)).differentiableAt (Metric.isOpen_ball.mem_nhds hz1)
  refine ⟨?_, ?_⟩
  · intro i k hk
    have hz0 := hne i k hk
    have hx0 : 0 < ‖z k‖ := norm_pos_iff.2 hz0
    have hx1 : ‖z k‖ < 1 := by linarith [hxk k]
    obtain ⟨h1, h2⟩ := xt_bounds hx0 hx1
    apply le_div_self (by positivity)
    · rw [← mul_pow]; unfold tOf; exact pow_pos h1 2
    · rw [← mul_pow]; unfold tOf; exact pow_le_one₀ h1.le h2
  · intro i
    have hr1 : 1 ≤ rComp L s i (ψ.symm z) := le_trans he1 (hre i)
    have hr2 : 1 ≤ rComp L s i (ψ.symm z) ^ 2 := by nlinarith
    cases hσ : σ i with
    | none =>
      have hev : (rComp L s i ∘ ψ.symm) =ᶠ[nhds z] (fun y => Real.exp 1 + f i y) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hz1] with y hy
        simp only [Function.comp, rComp]
        rw [hfeq i y hy, hσ]
        simp only [Option.elim, one_mul, Real.log_exp]
        ring
      have hd : fderiv ℝ (rComp L s i ∘ ψ.symm) z = fderiv ℝ (f i) z := by
        rw [hev.fderiv_eq, fderiv_const_add]
      have hg : gradSqAt ψ (rComp L s i) z w ≤ Cf i * ∑ k, ‖w k‖ ^ 2 := by
        unfold gradSqAt; rw [hd]
        have h := (hCf i z hzc).2 w
        have hπ := Real.pi_gt_three
        have h0 : 0 ≤ (fderiv ℝ (f i) z w) ^ 2 + (fderiv ℝ (f i) z (Complex.I • w)) ^ 2 := by positivity
        have hp : 1 / Real.pi ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        calc 1 / Real.pi * (((fderiv ℝ (f i) z w) ^ 2 + (fderiv ℝ (f i) z (Complex.I • w)) ^ 2) / 4)
            ≤ 1 * (((fderiv ℝ (f i) z w) ^ 2 + (fderiv ℝ (f i) z (Complex.I • w)) ^ 2) / 4) :=
              mul_le_mul_of_nonneg_right hp (by positivity)
          _ ≤ Cf i * ∑ k, ‖w k‖ ^ 2 := by linarith
      have hT0 : 0 ≤ gradSqAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z) ^ 2 :=
        div_nonneg (gradSqAt_nonneg _ _ _ _) (sq_nonneg _)
      have hT : gradSqAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z) ^ 2 ≤ Cf i * ∑ k, ‖w k‖ ^ 2 :=
        le_trans (div_le_self (gradSqAt_nonneg _ _ _ _) hr2) hg
      simp only [Option.elim]
      refine ⟨?_, ?_⟩
      · have := mul_le_mul_of_nonneg_right (by linarith [hCfle i] : Cf i ≤ ∑ j, Cf j + 1) hS
        linarith
      · intro δ h0 _
        have := mul_nonneg (mul_nonneg h0.le (by linarith : (0:ℝ) ≤ ∑ j, Cf j + 1)) hS
        simp only [mul_zero, zero_div, zero_sub]
        linarith
    | some k =>
      have hz0 := hne i k hσ
      obtain ⟨hLd, hLsq⟩ := GlobalTheory.T.log_norm_sq_gradient_identity k z hz0
      have hopen : IsOpen (Metric.ball (0 : Fin e → ℂ) 1 ∩ {y | y k ≠ 0}) :=
        Metric.isOpen_ball.inter (isOpen_ne_fun (continuous_apply k) continuous_const)
      have hrv : ∀ y ∈ Metric.ball (0 : Fin e → ℂ) 1, y k ≠ 0 →
          rComp L s i (ψ.symm y) = Real.exp 1 - Real.log (‖y k‖ ^ 2) + f i y := by
        intro y hy hyk
        unfold rComp
        rw [hfeq i y hy, hσ]
        simp only [Option.elim]
        have : (0:ℝ) < ‖y k‖ ^ 2 := by have := norm_pos_iff.2 hyk; positivity
        rw [Real.log_mul this.ne' (Real.exp_pos _).ne', Real.log_exp]
        ring
      have hev : (rComp L s i ∘ ψ.symm) =ᶠ[nhds z]
          (fun y => Real.exp 1 - Real.log (‖y k‖ ^ 2) + f i y) := by
        filter_upwards [hopen.mem_nhds ⟨hz1, hz0⟩] with y hy
        exact hrv y hy.1 hy.2
      have hH : HasFDerivAt (rComp L s i ∘ ψ.symm)
          ((0 - fderiv ℝ (fun y : Fin e → ℂ => Real.log (‖y k‖ ^ 2)) z) + fderiv ℝ (f i) z) z :=
        (((hasFDerivAt_const (Real.exp 1) z).sub hLd.hasFDerivAt).add
          (hfd i).hasFDerivAt).congr_of_eventuallyEq hev
      have hd := hH.fderiv
      have hx0 : 0 < ‖z k‖ := norm_pos_iff.2 hz0
      have hxM : ‖z k‖ < Real.exp (-M) := lt_of_le_of_lt (hxk k) hzM
      have hlogM : M < -Real.log ‖z k‖ := by
        have := Real.log_lt_log hx0 hxM; rw [Real.log_exp] at this; linarith
      have h2t : 2 * Real.pi * tOf (z k) = -Real.log ‖z k‖ := by
        unfold tOf; field_simp
      have hlog2 : Real.log (‖z k‖ ^ 2) = -(2 * (2 * Real.pi * tOf (z k))) := by
        rw [h2t, Real.log_pow]; push_cast; ring
      have hr := hrv z hz1 hz0
      rw [hlog2] at hr
      have hfz := abs_le.1 (hCf i z hzc).1
      have hCi := hCfle i
      have hMpos : 0 < M := by have := Real.exp_pos 1; linarith
      have hπ := Real.pi_pos
      have ht0 : 0 < tOf (z k) := by
        have : 0 < 2 * Real.pi * tOf (z k) := by linarith
        exact pos_of_mul_pos_right this (by positivity)
      have hrA : 2 * Real.pi * tOf (z k) ≤ rComp L s i (ψ.symm z) := by linarith
      have hrB : rComp L s i (ψ.symm z) ≤ 6 * Real.pi * tOf (z k) := by linarith
      have hab : (fderiv ℝ (fun y : Fin e → ℂ => Real.log (‖y k‖ ^ 2)) z w) ^ 2
          + (fderiv ℝ (fun y : Fin e → ℂ => Real.log (‖y k‖ ^ 2)) z (Complex.I • w)) ^ 2
          = 4 * (‖w k‖ ^ 2 / (‖z k‖ ^ 2 * tOf (z k) ^ 2)) * tOf (z k) ^ 2 := by
        rw [hLsq w]; field_simp
      have hgeq : gradSqAt ψ (rComp L s i) z w = 1 / Real.pi *
          (((-(fderiv ℝ (fun y : Fin e → ℂ => Real.log (‖y k‖ ^ 2)) z w) + fderiv ℝ (f i) z w) ^ 2
          + (-(fderiv ℝ (fun y : Fin e → ℂ => Real.log (‖y k‖ ^ 2)) z (Complex.I • w))
              + fderiv ℝ (f i) z (Complex.I • w)) ^ 2) / 4) := by
        unfold gradSqAt; rw [hd]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.zero_apply, zero_sub, ContinuousLinearMap.neg_apply]
      simp only [Option.elim]
      rw [hgeq]
      exact core hab (by positivity) ((hCf i z hzc).2 w) hS (hCf0 i) (by linarith) ht0 hrA hrB hr1

end GlobalTheory.CompBounds
