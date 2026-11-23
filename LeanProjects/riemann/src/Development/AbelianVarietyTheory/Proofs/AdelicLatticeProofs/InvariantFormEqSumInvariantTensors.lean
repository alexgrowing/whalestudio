import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleKroneckerPowerTransposeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LeftTranslateMatrixPolyTensorFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LeftTranslateMatrixPolyCompletelyReducibleStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsReynoldsOfCompletelyReducibleStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem invariant_form_eq_sum_invariant_tensors : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∀ (n : ℕ) (F : MvPolynomial (ι × ι) ℂ), IsInv Γ F → F.IsHomogeneous n → ∃ l : (Fin n → ι) → (Fin n → ι) → ℂ, (∀ b, ∀ g ∈ Γ, l b ᵥ* tpow n g = l b) ∧ ∀ y : Matrix ι ι ℂ, evC F y = ∑ b, (l b ᵥ* tpow n y) b := by
  intro ι _ _ Γ hP hS n F hF hhom
  obtain ⟨-, hinv, -, hp⟩ := GlobalTheory.T.leftTranslateMatrixPoly_tensorForm_properties ι
  obtain ⟨p, hpev, hpl, hpsurj⟩ := hp n
  obtain ⟨l, hl⟩ := hpsurj F hhom
  obtain ⟨R₁, h1a, -, -, h1d, -, -⟩ := GlobalTheory.T.exists_reynolds_of_completelyReducible' ((Fin n → ι) → ℂ)
    ((fun g => Matrix.toLin' (tpow n g)ᵀ) '' Γ) (by
      intro U hU
      obtain ⟨U', hU', hc⟩ := GlobalTheory.T.completelyReducible_kroneckerPower_transpose ι Γ hP hS n U (by
        rintro _ ⟨g, hg, rfl⟩ v hv
        simpa [Matrix.toLin'_apply] using hU _ ⟨g, hg, rfl⟩ v hv)
      refine ⟨U', ?_, hc⟩
      rintro _ ⟨g, hg, rfl⟩ v hv
      simpa [Matrix.toLin'_apply] using hU' _ ⟨g, hg, rfl⟩ v hv)
  obtain ⟨R₂, -, h2b, h2c, -, -, -⟩ := GlobalTheory.T.exists_reynolds_of_completelyReducible' (MvPolynomial (ι × ι) ℂ)
    ((fun g => (ltr g).toLinearMap) '' Γ) (by
      intro U hU
      obtain ⟨U', hU', hc⟩ := GlobalTheory.T.leftTranslateMatrixPoly_completelyReducible ι Γ hP hS U (fun g hg f hf => hU _ ⟨g, hg, rfl⟩ f hf)
      refine ⟨U', ?_, hc⟩
      rintro _ ⟨g, hg, rfl⟩ v hv
      exact hU' g hg v hv)
  have hfix : ∀ v, ∀ g ∈ Γ, R₁ v ᵥ* tpow n g = R₁ v := by
    intro v g hg
    have := h1a v _ ⟨g, hg, rfl⟩
    simpa [Matrix.toLin'_apply, Matrix.mulVec_transpose] using this
  have hkill : ∀ b, ∀ x ∈ Submodule.span ℂ
      {x | ∃ s ∈ ((fun g => Matrix.toLin' (tpow n g)ᵀ) '' Γ), ∃ w, x = s w - w}, R₂ (p b x) = 0 := by
    intro b x hx
    have hle : Submodule.span ℂ
        {x | ∃ s ∈ ((fun g => Matrix.toLin' (tpow n g)ᵀ) '' Γ), ∃ w, x = s w - w}
        ≤ LinearMap.ker (R₂ ∘ₗ p b) := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨g, hg, rfl⟩, w, rfl⟩
      have h := h2c (p b w) _ ⟨g, hg, rfl⟩
      simp only [AlgHom.toLinearMap_apply, hpl] at h
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, map_sub,
        Matrix.toLin'_apply, Matrix.mulVec_transpose, h, sub_self]
    exact hle hx
  have hb : ∀ b v, R₂ (p b v) = p b (R₁ v) := by
    intro b v
    have h0 := hkill b _ (h1d v)
    rw [map_sub, map_sub, sub_eq_zero] at h0
    rw [h0]
    apply h2b
    rintro _ ⟨g, hg, rfl⟩
    simp only [AlgHom.toLinearMap_apply, hpl, hfix v g hg]
  have hRF : R₂ F = F := by
    apply h2b
    rintro _ ⟨g, hg, rfl⟩
    exact (hinv Γ F).1 hF g hg
  have hF' : F = ∑ b, p b (R₁ (l b)) := by
    rw [← hRF, hl, map_sum]
    exact Finset.sum_congr rfl fun b _ => hb b _
  refine ⟨fun b => R₁ (l b), fun b g hg => hfix _ g hg, fun y => ?_⟩
  rw [hF']
  simp only [← hpev]
  unfold evC
  rw [map_sum]

end GlobalTheory.ClassFin
