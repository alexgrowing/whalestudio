import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KernInvariantSymmPos
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeasurePreservingMulLeft

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

private theorem det_sgnM_eq_prod_sgn {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) : (sgnM X).det = ∏ a : Fin r, ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
  simp [sgnM, Matrix.det_diagonal]

theorem normSq_det_of_isONFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {X : Data E r} {x : Frame X.Ψ r} (hx : IsONFr X x) (τ : X.Ψ) :
    normSq (mat x τ).det = ‖(X.Gm.map τ.1).det‖⁻¹ := by

  have hdet := congrArg Matrix.det (hx τ)
  rw [GlobalTheory.SW.Slab.det_gram, det_sgnM_eq_prod_sgn X] at hdet
  have hG : (X.Gm.map τ.1).det = τ.1 X.Gm.det := (RingHom.map_det τ.1 X.Gm).symm
  have hn := congrArg norm hdet
  rw [norm_mul, norm_mul, Complex.norm_conj, norm_prod] at hn
  simp only [GlobalTheory.SW.Slab.norm_sgn, Finset.prod_const_one] at hn
  rw [hG, Complex.normSq_eq_norm_sq]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hn]
  ring

theorem kZero_onFr_const_entire : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → (∃ κ : ℝ, 0 < κ ∧ ∀ x : Frame X.Ψ r, IsONFr X x → x ∈ X.dom ∧ kZero X idx x x (0 : Fin n → Fin g → ℂ) 0 = κ) ∧ ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, Differentiable ℂ (fun p : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) => kZero X idx x₁ x₂ p.1 p.2) := by
  intro E _ _ _ r X g q0 hr bas idx n _ _
  refine ⟨⟨∏ τ : X.Ψ, ‖(X.Gm.map τ.1).det‖⁻¹ ^ (n / 2), ?_, fun x hx => ⟨?_, ?_⟩⟩, ?_⟩
  ·
    refine Finset.prod_pos fun τ _ => pow_pos (inv_pos.mpr (norm_pos_iff.mpr ?_)) _
    exact GlobalTheory.SW.KernSym.det_map_Gm X τ
  ·
    obtain ⟨δ₀, hδ₀, hs⟩ := GlobalTheory.SW.thin_slab E r X
    obtain ⟨-, hsub, hon, -⟩ := hs δ₀ hδ₀ le_rfl
    exact hsub (hon x hx)
  ·

    rw [GlobalTheory.SW.KernSym.kZero_ortho idx hx]
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.exp_zero, mul_one]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => by rw [normSq_det_of_isONFr hx τ]
  ·
    intro x₁ _ x₂ _ p
    exact (GlobalTheory.SW.KernSym.analyticAt_kZero X idx x₁ x₂ p).differentiableAt

end GlobalTheory.Ker
