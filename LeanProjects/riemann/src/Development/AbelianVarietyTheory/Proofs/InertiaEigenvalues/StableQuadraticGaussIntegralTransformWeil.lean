import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGroupSignMulAndNegOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralMulNormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussAtUniformiserStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.WeilQuad
open scoped Pointwise

theorem isStableGauss_unique {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K)
    {G G' : ℂ} (h : IsStableGauss A ψ x μ u G) (h' : IsStableGauss A ψ x μ u G') : G = G' := by
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  obtain ⟨Λ₀, ho, hc, hG⟩ := h
  obtain ⟨Λ₁, ho', hc', hG'⟩ := h'
  have hs : ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) = (Λ₀ : Set A.L) + (Λ₁ : Set A.L) := AddSubgroup.add_normal Λ₀ Λ₁
  have hO : IsOpen ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) := AddSubgroup.isOpen_mono le_sup_left ho
  have hC : IsCompact ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) := by rw [hs]; exact hc.add hc'
  rw [← hG _ hO hC le_sup_left, ← hG' _ hO hC le_sup_right]

theorem absK_units_mul {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) (a b : A.Kˣ) :
    A.absK ((a * b : A.Kˣ) : A.K) = A.absK a * A.absK b := by
  simp [Et.absK]

theorem absK_units_ne {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) (a : A.Kˣ) : A.absK (a : A.K) ≠ 0 := by
  simp only [Et.absK, Units.isUnit, dite_true, IsUnit.unit_of_val_units, ne_eq, NNReal.coe_eq_zero]
  exact ((Group.isUnit a).map (distribHaarChar A.K)).ne_zero

theorem gauss_transform : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (u : A.Kˣ) (G G₁ : ℂ), IsStableGauss A ψ x μ u G → IsStableGauss A ψ x μ 1 G₁ → G = G₁ * ω u * ((A.absK u : ℂ))⁻¹ := by
  intro F E _ _ _ _ _ A ψ x μ ω hH u G G₁ hG hG₁
  have hω := hH.2.2.2.2
  by_cases hu : ∃ y, A.NL y = u
  · have h1 := GlobalTheory.T.stableQuadraticGaussIntegral_mul_norm F E A ψ x μ ω hH 1 u hu G₁ (by simpa using hG₁)
    rw [one_mul] at h1
    rw [isStableGauss_unique A ψ x μ _ hG h1, (hω u).1 hu]; ring
  · obtain ⟨ϖ, hϖ, hGϖ⟩ := GlobalTheory.T.exists_nonNorm_uniformizer_isStableGauss F E A ψ x μ ω hH G₁ hG₁
    have hps : ϖ * (ϖ⁻¹ * u) = u := mul_inv_cancel_left ϖ u
    have hs : ∃ y, A.NL y = ((ϖ⁻¹ * u : A.Kˣ) : A.K) := by
      by_contra hs
      have hm := (GlobalTheory.T.normGroupSign_mul_and_neg_one F E A ψ x μ ω hH).1 ϖ (ϖ⁻¹ * u)
      rw [hps, (hω u).2 hu, (hω ϖ).2 hϖ, (hω _).2 hs] at hm
      norm_num at hm
    have h2 := GlobalTheory.T.stableQuadraticGaussIntegral_mul_norm F E A ψ x μ ω hH ϖ (ϖ⁻¹ * u) hs _ hGϖ
    rw [hps] at h2
    rw [isStableGauss_unique A ψ x μ _ hG h2, (hω u).2 hu]
    have e1 := absK_units_ne A ϖ
    have e2 := absK_units_ne A (ϖ⁻¹ * u)
    conv_rhs => rw [← hps, absK_units_mul]
    push_cast
    field_simp

end GlobalTheory.JR.WeilQuad
