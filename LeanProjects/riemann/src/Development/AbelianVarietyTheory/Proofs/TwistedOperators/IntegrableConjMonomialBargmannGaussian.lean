import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl

theorem integrable_vcx_prod {ι : Type} [Fintype ι] {a b : ℕ} (g : ι → Fin b → Fin a → ℂ → ℂ)
    (hg : ∀ τ i j, Integrable (g τ i j)) :
    Integrable fun z : VCx ι a b => ∏ τ, ∏ i, ∏ j, g τ i j (z τ i j) := by
  have h1 : ∀ τ i, Integrable (fun w : Fin a → ℂ => ∏ j, g τ i j (w j)) := fun τ i =>
    Integrable.fintype_prod (f := fun j (w : ℂ) => g τ i j w) (hg τ i)
  have h2 : ∀ τ, Integrable (fun w : Fin b → Fin a → ℂ => ∏ i, ∏ j, g τ i j (w i j)) := fun τ =>
    Integrable.fintype_prod (f := fun i (w : Fin a → ℂ) => ∏ j, g τ i j (w j)) (h1 τ)
  exact Integrable.fintype_prod (f := fun τ (w : Fin b → Fin a → ℂ) => ∏ i, ∏ j, g τ i j (w i j)) h2

theorem exp_gq_eq_prod {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) (z : VCx ι a b) :
    (Real.exp (-gq c z / 2) : ℂ) = ∏ τ, ∏ i, ∏ j, (Real.exp (-(c τ * ‖z τ i j‖ ^ 2) / 2) : ℂ) := by
  have h : -gq c z / 2 = ∑ τ, ∑ i, ∑ j, (-(c τ * ‖z τ i j‖ ^ 2) / 2) := by
    simp [gq, Finset.sum_div, Finset.sum_neg_distrib, neg_div]
  rw [h]
  simp only [Real.exp_sum]
  push_cast
  rfl

theorem integrable_conj_pow_mul_gauss (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable fun w : ℂ => conj w ^ n * (Real.exp (-(c * ‖w‖ ^ 2) / 2) : ℂ) := by
  have h := GlobalTheory.integrable_norm_pow_mul_exp_neg_mul_norm_sq (E := ℂ) n (b := c / 2) (by positivity)
  refine h.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun w => ?_)
  rw [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  apply le_of_eq
  congr 2
  ring

theorem integrable_exp_bargmann_mul_gauss (u : ℂ) {c : ℝ} (hc : 0 < c) :
    Integrable fun w : ℂ => Complex.exp ((c : ℂ) * u * conj w) * (Real.exp (-(c * ‖w‖ ^ 2) / 2) : ℂ) := by
  have h := (GlobalTheory.integrable_exp_neg_mul_norm_sq (E := ℂ) (b := c / 4) (by positivity)).const_mul
    (Real.exp (c * ‖u‖ ^ 2))
  refine h.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun w => ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : ((c : ℂ) * u * conj w).re ≤ c * (‖u‖ * ‖w‖) := by
    calc _ ≤ ‖(c : ℂ) * u * conj w‖ := Complex.re_le_norm _
      _ = c * (‖u‖ * ‖w‖) := by
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hc.le]
        ring
  have h2 : ‖u‖ * ‖w‖ ≤ ‖u‖ ^ 2 + ‖w‖ ^ 2 / 4 := by nlinarith [sq_nonneg (‖u‖ - ‖w‖ / 2)]
  have h3 := mul_le_mul_of_nonneg_left h2 hc.le
  nlinarith

theorem integrable_conjMono_bargmann_gauss : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) →
    (∀ m : DVar ι a b →₀ ℕ, Integrable fun z => conjMono m z * (Real.exp (-gq c z / 2) : ℂ)) ∧
      ∀ z₀ : VCx ι a b, Integrable fun z => Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) := by
  intro ι _ a b c hc
  constructor
  · intro m
    have h := integrable_vcx_prod (fun τ i j w => conj w ^ m (τ, i, j) * (Real.exp (-(c τ * ‖w‖ ^ 2) / 2) : ℂ))
      (fun τ i j => integrable_conj_pow_mul_gauss _ (hc τ))
    refine h.congr (ae_of_all _ fun z => ?_)
    dsimp only
    rw [conjMono, exp_gq_eq_prod, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [Fintype.prod_prod_type, Finset.prod_mul_distrib]
  · intro z₀
    have h := integrable_vcx_prod (fun τ i j w => Complex.exp ((c τ : ℂ) * z₀ τ i j * conj w) *
      (Real.exp (-(c τ * ‖w‖ ^ 2) / 2) : ℂ)) (fun τ i j => integrable_exp_bargmann_mul_gauss _ (hc τ))
    refine h.congr (ae_of_all _ fun z => ?_)
    dsimp only
    rw [bk, exp_gq_eq_prod]
    simp only [Complex.exp_sum, Finset.prod_mul_distrib]

end GlobalTheory.FockTransl

end
