import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg

noncomputable section

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix

namespace GlobalTheory.RealWeil

theorem integral_norm_sq_eq_norm_toLp_sq {l : Type} [Fintype l] (g : Sch l) :
    ∫ x, ‖g x‖ ^ 2 = ‖g.toLp 2 volume‖ ^ 2 := by
  rw [SchwartzMap.norm_toLp' (by simp) (by simp)]
  have h2 : (2 : ENNReal).toReal = 2 := by simp
  simp only [h2]
  have hn : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℝ) := integral_nonneg fun x => by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
  norm_num

theorem metaplectic_oneParam_schwartz : GlobalTheory.Published.RealMetaplecticRepresentation →
    ∀ (l : Type) [Fintype l] [DecidableEq l] [Nonempty l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ),
      X ∈ LieAlgebra.Symplectic.sp l ℝ → ∃ U : ℝ → Sch l →ₗ[ℂ] Sch l, (∀ s t f, U (s + t) f = U s (U t f)) ∧
        (∀ f, U 0 f = f) ∧
        (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (NormedSpace.exp (t • X) *ᵥ w) ⇑(U t f)) ∧
        (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) ∧ ∀ f y, HasDerivAt (fun t => U t f y) (quad X f y) 0 := by
  intro hMp l _ _ _ X hX
  obtain ⟨G, _, _, _, pr, om, omS, -, -, h3, h4, h5, h6⟩ := hMp l
  obtain ⟨γ, -, h0, hadd, hpr, hd⟩ := h6 X hX
  refine ⟨fun t => (omS (γ t)).toLinearMap, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t f
    simp only [ContinuousLinearMap.coe_coe, hadd, map_mul, ContinuousLinearMap.mul_apply]
  · intro f
    simp [h0]
  · intro t w f f₁ h
    simp only [ContinuousLinearMap.coe_coe]
    rw [← hpr t]
    have hL : f₁.toLp 2 = rho w (f.toLp 2) := by
      refine Lp.ext ((SchwartzMap.coeFn_toLp f₁ 2 volume).trans ?_)
      refine Filter.EventuallyEq.symm ((coeFn_rho w _).trans ?_)
      rw [h]
      exact rhoFun_congr w (SchwartzMap.coeFn_toLp f 2 volume)
    have key : (omS (γ t) f₁).toLp 2 =
        rho ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ((omS (γ t) f).toLp 2) := by
      rw [← h4, hL, h3, h4]
    have hae : ⇑(omS (γ t) f₁) =ᵐ[volume]
        rhoFun ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ⇑(omS (γ t) f) := by
      refine (SchwartzMap.coeFn_toLp (omS (γ t) f₁) 2 volume).symm.trans ?_
      rw [key]
      refine (coeFn_rho _ _).trans ?_
      exact rhoFun_congr _ (SchwartzMap.coeFn_toLp (omS (γ t) f) 2 volume)
    have hc : Continuous (rhoFun ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ⇑(omS (γ t) f)) :=
      (continuous_phase _).mul ((omS (γ t) f).continuous.comp (continuous_id.add continuous_const))
    exact (Continuous.ae_eq_iff_eq volume (omS (γ t) f₁).continuous hc).1 hae
  · intro t f
    simp only [ContinuousLinearMap.coe_coe]
    rw [integral_norm_sq_eq_norm_toLp_sq, integral_norm_sq_eq_norm_toLp_sq, ← h4, LinearIsometryEquiv.norm_map]
  · intro f y
    let lam : Sch l →L[ℂ] ℂ :=
      (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)
    have hlam : ∀ g : Sch l, lam g = g y := fun g => rfl
    have := (metaplectic_schwartz_smooth h3 h4 h5).2.2 lam X hX γ h0 hpr hd f
    simpa only [hlam, ContinuousLinearMap.coe_coe] using this

end GlobalTheory.RealWeil

end
