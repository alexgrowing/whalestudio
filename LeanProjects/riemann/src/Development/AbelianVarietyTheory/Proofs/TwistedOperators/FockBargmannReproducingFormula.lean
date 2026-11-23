import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianConjMonomialMomentEqTaylorCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumFinsuppProdPowDivFactorialExpStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumTaylorSeriesDerivAtOriginCoordinateSpaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableGaussianExpLinearNormTermComplexMatrixStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

namespace GlobalTheory.FockRepr

theorem expand_real (κ : Type) [Fintype κ] (x : κ → ℝ) :
    HasSum (fun m : κ →₀ ℕ => m.prod fun k n => x k ^ n / (n.factorial : ℝ)) (Real.exp (∑ k, x k)) := by
  have h := GlobalTheory.T.hasSum_finsupp_prod_pow_div_factorial_exp_sum κ (fun k => (x k : ℂ))
  rw [← Complex.ofReal_sum, ← Complex.ofReal_exp] at h
  refine Complex.hasSum_ofReal.mp ?_
  convert h using 1
  funext m
  simp only [Finsupp.prod, Complex.ofReal_prod, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]

theorem conjMono_continuous {ι : Type} [Fintype ι] {a b : ℕ} (m : DVar ι a b →₀ ℕ) : Continuous (conjMono m) := by
  unfold conjMono Finsupp.prod; fun_prop

theorem gq_continuous {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) : Continuous (gq (a := a) (b := b) c) := by
  unfold gq; fun_prop

theorem bargmann_repr : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ G : VCx ι a b → ℂ, Differentiable ℂ G → (∃ M : ℝ, ∀ z, ‖G z‖ ≤ M * Real.exp (gq c z / 2)) → ∀ z₀, G z₀ = ((∏ τ, (c τ / Real.pi) ^ (a * b) : ℝ) : ℂ) * ∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z := by
  intro ι _ a b c hc G hG ⟨M, hM⟩ z₀
  have hbk : ∀ z, bk c z₀ z = ∑ k : DVar ι a b, (c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2) := by
    intro z; simp only [bk, Fintype.sum_prod_type]
  let coef : (DVar ι a b →₀ ℕ) → ℂ := fun m => m.prod fun k n => ((c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2) ^ n / (n.factorial : ℂ)
  have hcm : ∀ (m : DVar ι a b →₀ ℕ) z, coef m * conjMono m z = m.prod fun k n => ((c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2)) ^ n / (n.factorial : ℂ) := by
    intro m z
    simp only [coef, conjMono, ← Finsupp.prod_mul]
    refine Finset.prod_congr rfl fun k _ => ?_
    ring
  let F : (DVar ι a b →₀ ℕ) → VCx ι a b → ℂ := fun m z => coef m * (conjMono m z * (Real.exp (-gq c z) : ℂ) * G z)
  have hlim : ∀ z, HasSum (fun m => F m z) (Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z) := by
    intro z
    have := (GlobalTheory.T.hasSum_finsupp_prod_pow_div_factorial_exp_sum (DVar ι a b) (fun k => (c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2))).mul_right ((Real.exp (-gq c z) : ℂ) * G z)
    rw [← hbk] at this
    have e : (fun m => F m z) = fun m => (m.prod fun k n => ((c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2)) ^ n / (n.factorial : ℂ)) * ((Real.exp (-gq c z) : ℂ) * G z) := by
      funext m
      rw [← hcm]
      simp only [F]
      ring
    rw [e, mul_assoc]
    exact this
  have hnorm : ∀ m z, ‖F m z‖ = (m.prod fun k n => (‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) ^ n / (n.factorial : ℝ)) * (Real.exp (-gq c z) * ‖G z‖) := by
    intro m z
    have e1 : F m z = (coef m * conjMono m z) * ((Real.exp (-gq c z) : ℂ) * G z) := by simp only [F]; ring
    rw [e1, hcm, norm_mul, norm_mul, Finsupp.prod, Finsupp.prod, norm_prod, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_div, norm_pow, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
  have hnsum : ∀ z, HasSum (fun m => ‖F m z‖) (Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * ‖G z‖)) := by
    intro z
    simp only [hnorm]
    exact (expand_real (DVar ι a b) _).mul_right _
  have hGc : Continuous G := hG.continuous
  have hFc : ∀ m, Continuous (F m) := by
    intro m
    have h1 := conjMono_continuous m
    have h2 := gq_continuous (a := a) (b := b) c
    simp only [F]
    fun_prop
  have hS : Continuous fun z : VCx ι a b => ∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖ := by
    fun_prop
  have hint : Integrable (fun z => ∑' m, ‖F m z‖) := by
    have e : (fun z => ∑' m, ‖F m z‖) = fun z => Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * ‖G z‖) := by
      funext z; exact (hnsum z).tsum_eq
    rw [e]
    refine ((GlobalTheory.T.integrable_gaussian_exp_linear_norm_term_complex_matrix ι a b c hc z₀).const_mul M).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have h2 := gq_continuous (a := a) (b := b) c
      exact Continuous.aestronglyMeasurable (by fun_prop)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hz := hM z
      calc Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * ‖G z‖)
          ≤ Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * (M * Real.exp (gq c z / 2))) := by
            gcongr
        _ = M * Real.exp ((∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2) := by
            rw [show (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2
              = (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) + (-gq c z) + gq c z / 2 by ring,
              Real.exp_add, Real.exp_add]
            ring
  have hsumI : HasSum (fun m => ∫ z, F m z) (∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z) :=
    hasSum_integral_of_dominated_convergence (fun m z => ‖F m z‖) (fun m => (hFc m).aestronglyMeasurable)
      (fun m => Filter.Eventually.of_forall fun z => le_rfl) (Filter.Eventually.of_forall fun z => (hnsum z).summable)
      hint (Filter.Eventually.of_forall hlim)
  set P : ℝ := ∏ τ, (Real.pi / c τ) ^ (a * b) with hP
  have hFm : ∀ m, ∫ z, F m z = (P : ℂ) * ((m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ)) * derivAt0 G m) := by
    intro m
    simp only [F]
    rw [MeasureTheory.integral_const_mul, GlobalTheory.T.gaussian_conjMonomial_moment_eq_taylor_coefficient ι a b c hc G hG ⟨M, hM⟩ m]
    have hc' : coef m * (((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ)) : ℂ) = m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ) := by
      simp only [coef, Finsupp.prod, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have : (c k.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hc k.1).ne'
      push_cast
      rw [mul_pow, mul_div_assoc, mul_comm, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ this, one_pow, one_mul]
    rw [← hc']
    ring
  have hT := (GlobalTheory.T.hasSum_taylorSeries_derivAtOrigin_coordinateSpace ι a b G hG z₀).mul_left (P : ℂ)
  simp only [← hFm] at hT
  have heq := hsumI.unique hT
  rw [heq, ← mul_assoc]
  have h1 : (∏ τ, (c τ / Real.pi) ^ (a * b) : ℝ) * P = 1 := by
    rw [hP, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [← mul_pow]
    have : c τ ≠ 0 := (hc τ).ne'
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    rw [show c τ / Real.pi * (Real.pi / c τ) = 1 by field_simp, one_pow]
  rw [← Complex.ofReal_mul, h1, Complex.ofReal_one, one_mul]

end GlobalTheory.FockRepr
