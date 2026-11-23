import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarOfCommuteSchrodingerOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicativeHasDerivAtZeroStatement
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix

namespace GlobalTheory

theorem famChar_hasDerivAt : ∀ (l : Type) [Fintype l] (B : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (T U : ℝ → Sch l →ₗ[ℂ] Sch l) (Q : Sch l → EuclideanSpace ℝ l → ℂ), (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) → (∀ s t f, U (s + t) f = U s (U t f)) → (∀ f, U 0 f = f) → (∀ s t w, B (s + t) w = B s (B t w)) → (∀ w, B 0 w = w) → (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (B t w) ⇑(T t f)) → (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (B t w) ⇑(U t f)) → (∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ f y, Continuous fun t => T t f y) → (∀ f y, HasDerivAt (fun t => U t f y) (Q f y) 0) → ∃ c : ℂ, ∀ f y, HasDerivAt (fun t => T t f y) (Q f y + c * f y) 0 := by
  intro l _ B T U Q hT hT0 hU hU0 hB hB0 hTρ hUρ hTi hUi hTc hUd
  have hUinv : ∀ t f, U (-t) (U t f) = f := fun t f => by rw [← hU, neg_add_cancel, hU0]
  have hUinv' : ∀ t f, U t (U (-t) f) = f := fun t f => by rw [← hU, add_neg_cancel, hU0]

  have key : ∀ t, ∃ c : ℂ, ∀ f, T t f = c • U t f := by
    intro t
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_scalar_of_commute_schrodingerOperators l ((T t).comp (U (-t)))
      (fun f => by simp only [LinearMap.comp_apply]; rw [hTi, hUi])
      (fun w f f₁ h => by
        simp only [LinearMap.comp_apply]
        rw [hTρ t (B (-t) w) (U (-t) f) (U (-t) f₁) (hUρ (-t) w f f₁ h), ← hB, add_neg_cancel, hB0])
    refine ⟨c, fun f => ?_⟩
    have := hc (U t f)
    simp only [LinearMap.comp_apply, hUinv] at this
    exact this
  choose lam hlam using key
  set f₀ : Sch l := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)
  have hf₀ : f₀ 0 ≠ 0 := by simp [f₀]

  have hl0 : lam 0 = 1 := by
    have h := hlam 0 f₀
    rw [hT0, hU0] at h
    have h2 := congrArg (fun g : Sch l => g 0) h
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at h2
    have : (lam 0 - 1) * f₀ 0 = 0 := by linear_combination -h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hf₀)
  have hlmul : ∀ s t, lam (s + t) = lam s * lam t := by
    intro s t
    have h1 := hlam (s + t) (U (-(s + t)) f₀)
    rw [hUinv', hT, hlam t, map_smul, hlam s, ← hU, hUinv', smul_smul] at h1
    have h2 := congrArg (fun g : Sch l => g 0) h1
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at h2
    have : (lam s * lam t - lam (s + t)) * f₀ 0 = 0 := by linear_combination h2
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hf₀)).symm

  have hd : ContinuousAt (fun t => U t f₀ 0) 0 := (hUd f₀ 0).continuousAt
  have hd0 : U 0 f₀ 0 ≠ 0 := by rw [hU0]; exact hf₀
  have hlc : ContinuousAt lam 0 := by
    have hq : ContinuousAt (fun t => T t f₀ 0 / U t f₀ 0) 0 :=
      ((hTc f₀ 0).continuousAt).div hd hd0
    refine hq.congr ?_
    filter_upwards [hd.eventually_ne hd0] with t ht
    rw [hlam t f₀, SchwartzMap.smul_apply, smul_eq_mul, mul_div_assoc, div_self ht, mul_one]

  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_hasDerivAt_zero_of_continuousAt_of_map_add lam hl0 hlmul hlc
  refine ⟨c, fun f y => ?_⟩
  have hfun : (fun t => T t f y) = fun t => lam t * U t f y := by
    funext t; rw [hlam t f, SchwartzMap.smul_apply, smul_eq_mul]
  rw [hfun]
  have h := hc.mul (hUd f y)
  rw [hl0, hU0, one_mul, add_comm] at h
  exact h

end GlobalTheory
