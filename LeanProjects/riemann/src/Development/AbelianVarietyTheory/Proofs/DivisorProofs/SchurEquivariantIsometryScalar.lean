import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil

noncomputable section
open Complex
open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace Real FourierTransform ContDiff SchwartzMap

namespace GlobalTheory.RealWeil.FourierConjProductVanishing

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem ae_eq_zero_of_fourier_eq_zero {D : V → ℂ} (hD : Integrable D) (hF : ∀ ξ, 𝓕 D ξ = 0) :
    D =ᵐ[volume] 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hD.locallyIntegrable fun g hg hgc => ?_
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  set ψ : 𝓢(V, ℂ) := hg₁.toSchwartzMap hg₂ with hψ
  set φ : 𝓢(V, ℂ) := 𝓕⁻ ψ with hφ
  have h0 : ∀ x, (𝓕 φ) x = (g x : ℂ) := fun x => by
    rw [hφ, FourierTransform.fourier_fourierInv_eq, hψ]
    simp
  have h1 : ∫ x, g x • D x = ∫ x, (𝓕 φ) x * D x := by
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [h0, Complex.real_smul]
  have h2 : ∫ x, (𝓕 φ) x * D x = ∫ x, φ x * 𝓕 D x := by
    have := VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner (φ.integrable (μ := volume)) hD
    simpa using! this
  rw [h1, h2]
  simp [hF]

variable {l : Type} [Fintype l]

def pt (p q : EuclideanSpace ℝ l) : l ⊕ l → ℝ := Sum.elim (fun i => p i) (fun i => q i)

theorem pPart_pt (p q : EuclideanSpace ℝ l) : pPart (pt p q) = p := by
  ext i; simp [pPart, pt]

theorem qPart_pt (p q : EuclideanSpace ℝ l) : qPart (pt p q) = q := by
  ext i; simp [qPart, pt]

theorem fourier_conj_mul_eq_zero (f g : L2 l) (h : ∀ w, ⟪f, rho w g⟫_ℂ = 0) (p ξ : EuclideanSpace ℝ l) :
    𝓕 (fun x => conj (f x) * g (x + p)) ξ = 0 := by
  have h1 := h (pt p (-ξ))
  rw [L2.inner_def] at h1
  have h2 : ∫ x, conj (f x) * rhoFun (pt p (-ξ)) g x = 0 := by
    rw [← h1]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_rho (pt p (-ξ)) g] with x hx
    rw [hx, RCLike.inner_apply, mul_comm]
  have h3 : ∫ x, conj (f x) * rhoFun (pt p (-ξ)) g x =
      cexp (((π * ⟪p, -ξ⟫ : ℝ) : ℂ) * I) * 𝓕 (fun x => conj (f x) * g (x + p)) ξ := by
    rw [Real.fourier_eq', ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [rhoFun, phase, pPart_pt, qPart_pt, smul_eq_mul]
    have e : (((2 * π * ⟪-ξ, x⟫ + π * ⟪p, -ξ⟫ : ℝ) : ℂ) * I) =
        ((π * ⟪p, -ξ⟫ : ℝ) : ℂ) * I + ((-2 * π * ⟪x, ξ⟫ : ℝ) : ℂ) * I := by
      rw [inner_neg_left, real_inner_comm]
      push_cast
      ring
    rw [e, Complex.exp_add]
    ring
  rw [h2] at h3
  exact (mul_eq_zero.1 h3.symm).resolve_left (Complex.exp_ne_zero _)

theorem integrable_conj_mul_shift (f g : L2 l) (p : EuclideanSpace ℝ l) :
    Integrable (fun x => conj (f x) * g (x + p)) := by
  refine (L2.integrable_inner (𝕜 := ℂ) f (rho (pt p 0) g)).congr ?_
  filter_upwards [coeFn_rho (pt p 0) g] with x hx
  rw [hx, RCLike.inner_apply, mul_comm]
  simp [rhoFun, phase, pPart_pt, qPart_pt]

theorem eq_zero_or_eq_zero_of_inner_rho (f g : L2 l) (h : ∀ w, ⟪f, rho w g⟫_ℂ = 0) : f = 0 ∨ g = 0 := by
  have hz : ∀ p : EuclideanSpace ℝ l, ∀ᵐ x, ‖(f : _ → ℂ) x‖ₑ ^ 2 * ‖(g : _ → ℂ) (x + p)‖ₑ ^ 2 = 0 := by
    intro p
    filter_upwards [ae_eq_zero_of_fourier_eq_zero (integrable_conj_mul_shift f g p)
      (fourier_conj_mul_eq_zero f g h p)] with x hx
    have hx' : conj ((f : _ → ℂ) x) * (g : _ → ℂ) (x + p) = 0 := hx
    rcases mul_eq_zero.1 hx' with h0 | h0
    · rw [map_eq_zero] at h0
      simp [h0]
    · simp [h0]
  have hfm : Measurable fun x => ‖(f : _ → ℂ) x‖ₑ ^ 2 := (Lp.stronglyMeasurable f).measurable.enorm.pow_const 2
  have hgm : Measurable fun x => ‖(g : _ → ℂ) x‖ₑ ^ 2 := (Lp.stronglyMeasurable g).measurable.enorm.pow_const 2
  have hprod : (∫⁻ x, ‖(f : _ → ℂ) x‖ₑ ^ 2) * (∫⁻ x, ‖(g : _ → ℂ) x‖ₑ ^ 2) = 0 := by
    calc (∫⁻ x, ‖(f : _ → ℂ) x‖ₑ ^ 2) * (∫⁻ x, ‖(g : _ → ℂ) x‖ₑ ^ 2)
        = ∫⁻ x, ‖(f : _ → ℂ) x‖ₑ ^ 2 * ∫⁻ p, ‖(g : _ → ℂ) (x + p)‖ₑ ^ 2 := by
          rw [← lintegral_mul_const _ hfm]
          refine lintegral_congr fun x => ?_
          rw [lintegral_add_left_eq_self (fun y => ‖(g : _ → ℂ) y‖ₑ ^ 2) x]
      _ = ∫⁻ x, ∫⁻ p, ‖(f : _ → ℂ) x‖ₑ ^ 2 * ‖(g : _ → ℂ) (x + p)‖ₑ ^ 2 := by
          refine lintegral_congr fun x => ?_
          exact (lintegral_const_mul _ (hgm.comp (measurable_const_add x))).symm
      _ = ∫⁻ p, ∫⁻ x, ‖(f : _ → ℂ) x‖ₑ ^ 2 * ‖(g : _ → ℂ) (x + p)‖ₑ ^ 2 := by
          refine lintegral_lintegral_swap ?_
          exact ((hfm.comp measurable_fst).mul (hgm.comp measurable_add)).aemeasurable
      _ = 0 := by
          rw [← lintegral_zero]
          exact lintegral_congr fun p => lintegral_eq_zero_of_ae_eq_zero (hz p) |>.trans rfl
  have key : ∀ u : L2 l, (∫⁻ x, ‖(u : _ → ℂ) x‖ₑ ^ 2) = 0 → u = 0 := by
    intro u hu
    have hum : Measurable fun x => ‖(u : _ → ℂ) x‖ₑ ^ 2 := (Lp.stronglyMeasurable u).measurable.enorm.pow_const 2
    rw [lintegral_eq_zero_iff hum] at hu
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hu] with x hx
    simpa using hx
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact Or.inl (key f h0)
  · exact Or.inr (key g h0)

theorem rho_symm_apply (w : l ⊕ l → ℝ) (v : L2 l) :
    (rho w).symm v = (cexp (((π * sympl w (-w) : ℝ) : ℂ) * I))⁻¹ • rho (-w) v := by
  rw [LinearIsometryEquiv.symm_apply_eq, map_smul, rho_rho, add_neg_cancel, rho_zero,
    inv_smul_smul₀ (Complex.exp_ne_zero _)]

def opSet (l : Type) [Fintype l] : Set (L2 l →L[ℂ] L2 l) :=
  Set.range fun cw : ℂ × (l ⊕ l → ℝ) => cw.1 • ((rho cw.2).toContinuousLinearEquiv : L2 l →L[ℂ] L2 l)

theorem star_mem_opSet : ∀ A ∈ opSet l, star A ∈ opSet l := by
  rintro _ ⟨⟨c, w⟩, rfl⟩
  refine ⟨⟨conj c * (cexp (((π * sympl w (-w) : ℝ) : ℂ) * I))⁻¹, -w⟩, ?_⟩
  rw [star_smul, ContinuousLinearMap.star_eq_adjoint]
  ext v
  have e := congrArg (fun T : L2 l →L[ℂ] L2 l => T v) (LinearIsometryEquiv.adjoint_eq_symm (rho w))
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] at e ⊢
  rw [e, rho_symm_apply, smul_smul]
  rfl

theorem irreducible_opSet (S : Submodule ℂ (L2 l)) (hS : IsClosed (S : Set (L2 l)))
    (hst : ∀ A ∈ opSet l, ∀ v ∈ S, A v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  by_cases h0 : S = ⊥
  · exact Or.inl h0
  right
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  haveI : CompleteSpace S := hS.completeSpace_coe
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro f hf
  have hw : ∀ w, ⟪f, rho w g⟫_ℂ = 0 := by
    intro w
    have hm : rho w g ∈ S := by
      have := hst _ ⟨⟨1, w⟩, rfl⟩ g hg
      simpa using this
    exact Submodule.inner_left_of_mem_orthogonal hm hf
  exact (eq_zero_or_eq_zero_of_inner_rho f g hw).resolve_right hg0

end GlobalTheory.RealWeil.FourierConjProductVanishing

namespace GlobalTheory.RealWeil

open GlobalTheory.RealWeil.FourierConjProductVanishing in

theorem schur_rho_l2 : ∀ (l : Type) [Fintype l] (U : L2 l ≃ₗᵢ[ℂ] L2 l), (∀ w v, U (rho w v) = rho w (U v)) →
    ∃ a : ℂ, ∀ v, U v = a • v := by
  intro l _ U hU
  obtain ⟨c, hc⟩ := Formalism.MainNotions.BridgeCSchur.schur_bounded (opSet l) star_mem_opSet
    (fun S hS hst => irreducible_opSet S hS hst) (U.toContinuousLinearEquiv : L2 l →L[ℂ] L2 l) (by
      rintro _ ⟨⟨c, w⟩, rfl⟩
      ext v
      simp [hU])
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun T : L2 l →L[ℂ] L2 l => T v) hc
  simpa using this

end GlobalTheory.RealWeil
