import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MatRmulUnipMulHeadProj
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumPrincipalTorusAtOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableNormSiegelThetaSeriesTerms
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaCharacteristicsIffTestFunctionThetaSeriesStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.ThetaHol

theorem exists_corner {κ ι : Type} [Fintype κ] [Fintype ι] (τ : Matrix ι ι ℂ) (S : ℝ)
    (x : Matrix κ ι ℚ) : ∃ s : κ → ι → Bool, ∀ ζ : κ → ι → ℂ, ‖ζ‖ ≤ S →
      ‖cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))‖ ≤
      ‖cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) +
        2 * (qv (x k) ⬝ᵥ fun i => (if s k i then -S else S : ℝ) * I)))‖ := by
  refine ⟨fun k i => decide (0 ≤ x k i), fun ζ hζ => ?_⟩
  rw [Complex.norm_exp, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [mul_assoc, Complex.re_ofReal_mul, Complex.I_mul_re, Complex.im_sum, Complex.add_im,
    Complex.mul_im, dotProduct, qv, Complex.ratCast_re, Complex.ratCast_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero, mul_one,
    Complex.re_ofNat, Complex.im_ofNat, decide_eq_true_eq]
  refine mul_le_mul_of_nonneg_left (neg_le_neg (Finset.sum_le_sum fun k _ => ?_)) Real.pi_pos.le
  refine add_le_add le_rfl ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) zero_le_two
  have h1 : |(ζ k i).im| ≤ S := (Complex.abs_im_le_norm _).trans
    ((norm_le_pi_norm (ζ k) i).trans ((norm_le_pi_norm ζ k).trans hζ))
  have h2 := abs_le.mp h1
  split_ifs with h
  · have : (0 : ℝ) ≤ (x k i : ℝ) := by exact_mod_cast h
    nlinarith
  · have : (x k i : ℝ) < 0 := by exact_mod_cast lt_of_not_ge h
    nlinarith

theorem differentiable_thS {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {φ : Matrix κ ι ℚ → ℂ} (hφ : IsSB φ) {τ : Matrix ι ι ℂ} (hτ : τ ∈ Siegel ι) :
    Differentiable ℂ (thS φ τ) := by
  intro ζ₀
  let F : Matrix κ ι ℚ → (κ → ι → ℂ) → ℂ := fun x ζ => φ x *
    cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))
  let S : ℝ := ‖ζ₀‖ + 2
  let cor : (κ → ι → Bool) → κ → ι → ℂ := fun s k i => ((if s k i then -S else S : ℝ) : ℂ) * I
  choose s hs using fun x : Matrix κ ι ℚ => exists_corner τ S x
  have hFd : ∀ x, Differentiable ℂ (F x) := by
    intro x
    simp only [F, dotProduct]
    fun_prop
  have hbd : ∀ x, ∀ z : κ → ι → ℂ, ‖z‖ ≤ S → ‖F x z‖ ≤ ‖F x (cor (s x))‖ := by
    intro x z hz
    simp only [F, norm_mul]
    exact mul_le_mul_of_nonneg_left (hs x z hz) (norm_nonneg _)
  have hsum : Summable fun x => ‖F x (cor (s x))‖ := by
    have hfin : Summable fun x => ∑ t : κ → ι → Bool, ‖F x (cor t)‖ :=
      summable_sum fun t _ => SiegelSum.summable_norm_thetaTerm κ ι φ hφ τ hτ (cor t)
    refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) hfin
    exact Finset.single_le_sum (f := fun t => ‖F x (cor t)‖) (fun t _ => norm_nonneg _)
      (Finset.mem_univ (s x))
  have hder : ∀ x, ∀ ζ ∈ Metric.ball (0 : κ → ι → ℂ) (‖ζ₀‖ + 1),
      ‖fderiv ℂ (F x) ζ‖ ≤ 2 * ‖F x (cor (s x))‖ := by
    intro x ζ hζ
    have h := GlobalTheory.SCV.norm_fderiv_le_of_ball (f := F x) (c := ζ) (r := 1)
      (M := ‖F x (cor (s x))‖) one_pos (hFd x).differentiableOn (fun z hz => hbd x z (by
        rw [Metric.mem_ball, dist_eq_norm] at hz
        rw [Metric.mem_ball, dist_zero_right] at hζ
        have := norm_sub_norm_le z ζ
        simp only [S]
        linarith))
    simpa using h
  have h0 : ζ₀ ∈ Metric.ball (0 : κ → ι → ℂ) (‖ζ₀‖ + 1) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have key := hasFDerivAt_tsum_of_isPreconnected (hsum.mul_left 2) Metric.isOpen_ball
    (convex_ball _ _).isPreconnected (fun x ζ _ => (hFd x ζ).hasFDerivAt) hder h0
    (SiegelSum.summable_norm_thetaTerm κ ι φ hφ τ hτ ζ₀).of_norm h0
  exact key.differentiableAt

theorem differentiable_thA {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) {φ : TF n g} (hφ : IsSB φ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Differentiable ℂ (thA X bas idx φ x) := by
  have hτ := UnAct.tauMat_mem idx hs hx
  have hlin : Differentiable ℂ fun z : Fin n → Fin g → ℂ => fun k => hMat X bas idx x *ᵥ z k := by
    refine differentiable_pi.2 fun k => differentiable_pi.2 fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hth := (differentiable_thS hφ hτ).comp hlin
  have hq : Differentiable ℂ fun z : Fin n → Fin g → ℂ => ∑ k, (hMat X bas idx x *ᵥ z k) ⬝ᵥ
      imInv X bas idx x *ᵥ (hMat X bas idx x *ᵥ z k) := by
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  unfold thA
  exact ((hq.const_mul _).cexp.const_mul _).mul hth

end GlobalTheory.SW.ThetaHol

namespace GlobalTheory.SW

theorem theta_holomorphic_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (φ : TF n g), IsSB φ → ∀ P ∈ Harm.rowHighest ℂ c c', DifferentiableOn ℂ (thP X hr bas idx φ P) X.dom ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, thP X hr bas idx φ P (rmul x b) = bchar (wtOf X hr c c' n) b * thP X hr bas idx φ P x) ∧ (∀ γ, IsUn X γ → ∀ x ∈ X.dom, thP X hr bas idx (wG X bas idx γ φ) P (lact γ x) = thP X hr bas idx φ P x) ∧ ∀ x ∈ X.dom, AnalyticOnNhd ℂ (thA X bas idx φ x) Set.univ := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn c c' φ hφ P hP
  obtain ⟨m, a, b, t, ht⟩ := (GlobalTheory.T.thetaCharacteristics_iff_testFunction_thetaSeries E r X g q0 hr bas idx n hs hn).2 φ hφ
  have hH := Harm.isHarmonic_of_mem_rowHighest hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hd : DifferentiableOn ℂ (fun x => ∑ j, t j * thFr X hr bas idx n
        (fun k i => (a j k i : ℝ)) (fun k i => (b j k i : ℝ)) P x) X.dom :=
      DifferentiableOn.fun_sum fun j _ => (differentiableOn_thFr idx hs hr n _ _ hH).const_mul (t j)
    exact hd.congr fun x hx => ht P x hx
  · intro x hx u hu
    have hxu := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hu
    rw [ht P _ hxu, ht P x hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [thFr_rmul idx hr _ _ hs hP hx hu]
    ring
  · intro γ hγ x hx
    unfold thP
    rw [(wG_laws E r X g bas idx n hs hn γ hγ φ hφ).2.1 x hx]
  · intro x hx
    exact GlobalTheory.SCV.analyticOnNhd_of_differentiable (ThetaHol.differentiable_thA idx hs hφ hx) _

end GlobalTheory.SW
