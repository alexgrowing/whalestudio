import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem eq_zero_of_bounded_of_creation_eq {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R]
    (F : R → ℂ) (hF : Differentiable ℝ F) (C : ℝ) (hC : ∀ x, ‖F x‖ ≤ C) (u u' : R) (a b q : ℝ) (hq : 0 < q)
    (h : ∀ s t : ℝ, fderiv ℝ F (s • u - t • u') u - Complex.I * fderiv ℝ F (s • u - t • u') u' =
      Real.pi * Complex.I * ((a + t * q) - Complex.I * (b + s * q)) * F (s • u - t • u')) :
    F 0 = 0 := by
  let L : ℂ →L[ℝ] R := Complex.reCLM.smulRight u - Complex.imCLM.smulRight u'
  have hL : ∀ z : ℂ, L z = z.re • u - z.im • u' := fun z => rfl
  let re' : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  let im' : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM
  have hre : ∀ z : ℂ, re' z = (z.re : ℂ) := fun z => rfl
  have him : ∀ z : ℂ, im' z = (z.im : ℂ) := fun z => rfl
  let c1 : ℂ := -(Real.pi * Complex.I)
  let c2 : ℂ := -(Real.pi * q / 2)
  let φ : ℂ → ℂ := fun z => c1 * (a * re' z - b * im' z) + c2 * (re' z * re' z + im' z * im' z)
  let H : ℂ → ℂ := fun z => Complex.exp (φ z) * F (L z)
  have hHd : Differentiable ℂ H := by
    intro z
    have r := re'.hasFDerivAt (x := z)
    have i := im'.hasFDerivAt (x := z)
    have h1 := ((((r.const_mul (a : ℂ)).sub (i.const_mul (b : ℂ))).const_mul c1).add
      (((r.mul r).add (i.mul i)).const_mul c2)).cexp
    have h2 := (hF (L z)).hasFDerivAt.comp z (L.hasFDerivAt (x := z))
    have h3 : HasFDerivAt H _ z := h1.mul h2
    rw [differentiableAt_complex_iff_differentiableAt_real]
    refine ⟨h3.differentiableAt, ?_⟩
    rw [h3.fderiv]
    have e := h z.re z.im
    rw [← hL] at e
    have e1 : L 1 = u := by simp [hL]
    have eI : L Complex.I = -u' := by simp [hL]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, e1, eI, hre, him, smul_eq_mul, map_neg, Function.comp_apply,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.ofReal_zero, Complex.ofReal_one]
    generalize Complex.exp _ = E
    rw [sub_eq_iff_eq_add] at e
    rw [e]
    simp only [c1, c2]
    linear_combination (-(E * fderiv ℝ F (L z) u') + E * F (L z) * Real.pi * (-(z.im * q) + Complex.I * (b + z.re * q))) * Complex.I_mul_I
  have hn : ∀ z, ‖H z‖ ≤ C * Real.exp (-(Real.pi * q / 2) * ‖z‖ ^ 2) := by
    intro z
    have : (φ z).re = -(Real.pi * q / 2) * ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [φ, c1, c2, hre, him]
    simp only [H]
    rw [norm_mul, Complex.norm_exp, this, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (Real.exp_pos _).le
  have ht : Filter.Tendsto H (Filter.cocompact ℂ) (nhds 0) := by
    refine squeeze_zero_norm hn ?_
    have hp : -(Real.pi * q / 2) < 0 := by have := Real.pi_pos; have : 0 < Real.pi * q / 2 := by positivity
                                           linarith
    have t1 : Filter.Tendsto (fun z : ℂ => ‖z‖ ^ 2) (Filter.cocompact ℂ) Filter.atTop :=
      (Filter.tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop
    have t2 := (Real.tendsto_exp_atBot.comp (t1.const_mul_atTop_of_neg hp)).const_mul C
    simpa using t2
  have h0 := hHd.apply_eq_of_tendsto_cocompact 0 ht
  simp only [H, map_zero, mul_eq_zero, Complex.exp_ne_zero, false_or] at h0
  exact h0

theorem eq_zero_of_creation_eq_zero : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → (∀ u v, om v u = -om u v) → ∀ (f : G → ℂ), Sm ι f → (∀ w, ∃ C : ℝ, ∀ x, ‖f (w + ι x)‖ ≤ C) → ∀ u u' : R, 0 < om u u' → hD ι π om u f - Complex.I • hD ι π om u' f = 0 → f = 0 := by
  intro G R _ _ _ _ ι π om hπ hform hanti f hf hb u u' hq h0
  funext w
  obtain ⟨C, hC⟩ := hb w
  have hF : Differentiable ℝ fun x : R => f (w + ι x) := (hf w).differentiable (by simp)
  have huu : ∀ v, om v v = 0 := fun v => by have := hanti v v; linarith
  have key := eq_zero_of_bounded_of_creation_eq (fun x : R => f (w + ι x)) hF C hC u u'
    (om (π w) u) (om (π w) u') (om u u') hq (fun s t => by
      set x := s • u - t • u' with hx
      have e := congrFun h0 (w + ι x)
      have hfd : fderiv ℝ (fun y : R => f (w + ι x + ι y)) 0 = fderiv ℝ (fun y : R => f (w + ι y)) x := by
        have : (fun y : R => f (w + ι x + ι y)) = fun y => (fun y : R => f (w + ι y)) (x + y) := by
          funext y; simp only [map_add, add_assoc]
        rw [this, fderiv_comp_add_left (f := fun y : R => f (w + ι y)), add_zero]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hform f hf, hfd] at e
      have e1 : om (π (w + ι x)) u = om (π w) u + t * om u u' := by
        rw [map_add, hπ, map_add, LinearMap.add_apply, hx]
        simp [huu, hanti u u']
      have e2 : om (π (w + ι x)) u' = om (π w) u' + s * om u u' := by
        rw [map_add, hπ, map_add, LinearMap.add_apply, hx]
        simp [huu]
      rw [e1, e2] at e
      push_cast at e
      linear_combination e)
  simpa using key

end GlobalTheory.FockCompare
