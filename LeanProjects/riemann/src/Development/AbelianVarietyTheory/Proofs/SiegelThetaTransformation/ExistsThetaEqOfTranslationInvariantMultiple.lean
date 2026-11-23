import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensity
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFourierEntire

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.Onto

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem exponent_eq {x : Frame X.Ψ r}
    (h : ∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w)) (z p : Fin n → Fin g → ℂ) :
    -(π * I * ((∑ k, hx X bas idx x (z k) (p k)).im : ℝ)) +
      -(π / 2 * ∑ k, hx X bas idx x (z k + p k) (z k + p k)) =
    -(π / 2 * ∑ k, hx X bas idx x (z k) (z k)) +
      -(π * ∑ k, hx X bas idx x (z k + (1 / 2 : ℂ) • p k) (p k)) := by
  have h1 (k) : hx X bas idx x (z k + p k) (z k + p k) = hx X bas idx x (z k) (z k) +
      hx X bas idx x (z k) (p k) + conj (hx X bas idx x (z k) (p k)) +
      hx X bas idx x (p k) (p k) := by
    rw [← h]
    simp only [hx, mulVec_add, star_add, add_dotProduct, dotProduct_add]
    ring
  have h2 (k) : hx X bas idx x (z k + (1 / 2 : ℂ) • p k) (p k) = hx X bas idx x (z k) (p k) +
      1 / 2 * hx X bas idx x (p k) (p k) := by
    simp only [hx, mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]
  simp only [h1, h2, Finset.sum_add_distrib, ← Finset.mul_sum, ← map_sum]
  have h3 := Complex.sub_conj (∑ k, hx X bas idx x (z k) (p k))
  push_cast at h3
  linear_combination (π / 2 : ℂ) * h3

theorem exists_canonical (h τ W : Matrix (Fin g) (Fin g) ℂ) (hu : IsUnit h.det)
    (hτ : τ ∈ Siegel (Fin g)) (hW : W.IsSymm) (hY : W * τ.map (fun z => (z.im : ℂ)) = 1)
    {D : ℂ} (hD : D ≠ 0) {N : ℕ} (hN : 0 < N) {θ : (Fin n → Fin g → ℂ) → ℂ}
    (hθ : Differentiable ℂ θ)
    (key : ∀ a b : Fin n → Fin g → ℤ, ∃ p : Fin n → Fin g → ℂ,
      (∀ k, h *ᵥ p k = (fun i => (N * a k i : ℂ)) + τ *ᵥ fun i => (N * b k i : ℂ)) ∧
      ∀ z : Fin n → Fin g → ℂ, cexp (-(π * ∑ k, (h *ᵥ (z k + (1 / 2 : ℂ) • p k)) ⬝ᵥ W *ᵥ
        star (h *ᵥ p k))) * θ (fun k => z k + p k) = θ z) :
    ∃ φ : TF n g, IsSB φ ∧ ∀ z : Fin n → Fin g → ℂ,
      D * cexp (π / 2 * ∑ k, (h *ᵥ z k) ⬝ᵥ W *ᵥ (h *ᵥ z k)) * thS φ τ (fun k => h *ᵥ z k) = θ z := by
  obtain ⟨c, hcd⟩ : ∃ c : (Fin n → Fin g → ℂ) → ℂ,
    c = fun ζ => cexp (π / 2 * ∑ k, ζ k ⬝ᵥ W *ᵥ ζ k) := ⟨_, rfl⟩
  obtain ⟨Θ, hΘd⟩ : ∃ Θ : (Fin n → Fin g → ℂ) → ℂ,
    Θ = fun ζ => (D * c ζ)⁻¹ * θ fun k => h⁻¹ *ᵥ ζ k := ⟨_, rfl⟩
  have hc (ζ) : D * c ζ ≠ 0 := mul_ne_zero hD (hcd ▸ Complex.exp_ne_zero _)
  have hΘ : Differentiable ℂ Θ := by
    rw [hΘd]
    refine Differentiable.mul (Differentiable.inv ?_ hc) (hθ.comp ?_)
    · simp only [hcd, mulVec, dotProduct]
      fun_prop
    · refine differentiable_pi.2 fun k => differentiable_pi.2 fun i => ?_
      simp only [mulVec, dotProduct]
      fun_prop
  have main : ∀ (a b : Fin n → Fin g → ℤ) (ζ : Fin n → Fin g → ℂ),
      cexp (π * I * ∑ k, ((fun i => (N * b k i : ℂ)) ⬝ᵥ τ *ᵥ
        (fun i => (N * b k i : ℂ)) + 2 * ((fun i => (N * b k i : ℂ)) ⬝ᵥ ζ k) +
        (fun i => (N * a k i : ℂ)) ⬝ᵥ (fun i => (N * b k i : ℂ)))) *
      Θ (fun k => ζ k + ((fun i => (N * a k i : ℂ)) + τ *ᵥ fun i => (N * b k i : ℂ))) = Θ ζ := by
    intro a b ζ
    have hq (m : Fin g → ℤ) : qv (fun i => (N * m i : ℚ)) = fun i => (N * m i : ℂ) := by
      funext i; simp [qv]
    obtain ⟨p, hp, h1⟩ := key a b
    have h1 := h1 fun k => h⁻¹ *ᵥ ζ k
    have he := Finset.sum_congr (s₁ := Finset.univ) rfl fun (k : Fin n) _ =>
      heis_exponent _ _ hτ.1 hW hY (fun i => (N * a k i : ℚ)) (fun i => (N * b k i : ℚ)) (ζ k)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at he
    have he' := congrArg cexp he
    rw [Complex.exp_add, Complex.exp_add] at he'
    simp only [hq] at he'
    have h2 (k) : h⁻¹ *ᵥ (ζ k + ((fun i => (N * a k i : ℂ)) + τ *ᵥ fun i => (N * b k i : ℂ))) =
        h⁻¹ *ᵥ ζ k + p k := by
      rw [← hp, mulVec_add, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
    simp only [mulVec_add h, mulVec_smul h, hp, mulVec_mulVec, mul_nonsing_inv _ hu,
      one_mulVec] at h1
    simp only [hΘd, h2]
    rw [← h1, ← mul_assoc, ← mul_assoc]
    congr 1
    have h3 := hc ζ
    have h4 := hc fun k => ζ k + ((fun i => (N * a k i : ℂ)) + τ *ᵥ fun i => (N * b k i : ℂ))
    rw [mul_inv_eq_iff_eq_mul₀ h4, mul_assoc (_ * c ζ)⁻¹, eq_inv_mul_iff_mul_eq₀ h3]
    simp only [hcd]
    linear_combination D * he'
  obtain ⟨φ, hφ, h5⟩ := GlobalTheory.Ker.LevelTheta.exists_thS_eq n g τ hτ N hN Θ hΘ (fun a ζ => by
      have := main a 0 ζ
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, ← Pi.zero_def, mulVec_zero, add_zero,
        dotProduct_zero, zero_dotProduct, Finset.sum_const_zero, Complex.exp_zero, one_mul] at this
      exact this) (fun b ζ => by
      have := main 0 b ζ
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, ← Pi.zero_def, zero_add, add_zero,
        zero_dotProduct] at this
      exact this)
  refine ⟨φ, hφ, fun z => ?_⟩
  have h6 := hc fun k => h *ᵥ z k
  rw [h5]
  simp only [hΘd, hcd, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec] at h6 ⊢
  exact mul_inv_cancel_left₀ h6 (θ z)

theorem exists_thA_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ (N : ℕ), 0 < N → ∀ θ : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ θ → (∀ y : Matrix (Fin n) (Fin r) E, (∀ k, y k ∈ X.Λ) → ∀ v : WR X n, cexp (-(π * I * (EFR X v (N • embR X y) : ℝ))) * (gaussR X bas idx x (zR X idx x (v + N • embR X y)) * θ (zR X idx x (v + N • embR X y))) = gaussR X bas idx x (zR X idx x v) * θ (zR X idx x v)) → ∃ φ : TF n g, IsSB φ ∧ ∀ z, thA X bas idx φ x z = θ z := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn x hx' N hN θ hθ hinv
  obtain ⟨⟨L, hL⟩, him, -⟩ := GlobalTheory.Ker.zR_laws E r X g q0 hr bas idx n hs hn x hx'
  have hconj := (GlobalTheory.Dict.hx_laws E r X g bas idx n hs hn x hx').1
  have hu := isUnit_det_hMat idx hs hx'
  have key : ∀ y : Matrix (Fin n) (Fin r) E, (∀ k, y k ∈ X.Λ) → ∀ z : Fin n → Fin g → ℂ,
      cexp (-(π * ∑ k, hx X bas idx x (z k + (1 / 2 : ℂ) • (N • pv X idx x (y k)))
        (N • pv X idx x (y k)))) * θ (fun k => z k + N • pv X idx x (y k)) = θ z := by
    intro y hy z
    obtain ⟨v, rfl⟩ := L.surjective z
    have h1 : zR X idx x (N • embR X y) = fun k => N • pv X idx x (y k) := by
      rw [← hL, map_nsmul, hL]; rfl
    have h2 : zR X idx x (v + N • embR X y) = fun k => L v k + N • pv X idx x (y k) := by
      rw [← hL, map_add, hL (N • _), h1]; rfl
    have h3 := hinv y hy v
    rw [← him, h1, h2, ← hL v, gaussR, gaussR, ← mul_assoc, ← Complex.exp_add,
      exponent_eq idx hconj (L v) fun k => N • pv X idx x (y k), Complex.exp_add, mul_assoc] at h3
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) h3
  refine exists_canonical (hMat X bas idx x) (tauMat X bas idx x) (imInv X bas idx x) hu
    ⟨tauMat_isSymm idx hs hx', tauMat_im_posDef idx hs hx'⟩ (imInv_isSymm idx hs hx')
    (imInv_mul_im idx hs hx') (pow_ne_zero (n / 2) hu.ne_zero) hN hθ fun a b =>
    ⟨fun k => N • pv X idx x (bas (Sum.elim (a k) (b k))), fun k => ?_,
      key (Matrix.of fun k => (bas (Sum.elim (a k) (b k)) : Fin r → E)) fun k => (bas _).2⟩
  beta_reduce
  rw [← Nat.cast_smul_eq_nsmul ℂ, mulVec_smul, pv, hMat_mulVec_per_bas idx hs hx', smul_add,
    ← mulVec_smul]
  rfl

end GlobalTheory.Ker.Onto
