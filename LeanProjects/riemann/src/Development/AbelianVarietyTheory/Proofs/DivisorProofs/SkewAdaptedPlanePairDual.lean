import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EvTwist

theorem conj_ev : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ h₁ m, IsLevi H' 1 h₁ m →
        (∀ Φ ∈ schA F (Fin n × Fin d), (om₁ (1, h₁⁻¹) ∘ₗ e ∘ₗ om (1, m)) Φ ∈ schA F (Fin n × Fin d₁)) ∧
        (∀ z : Matrix (Fin n) (Fin d₁) (AE F E), ∀ Φ ∈ schA F (Fin n × Fin d), (om₁ (1, h₁⁻¹) ∘ₗ e ∘ₗ om (1, m)) (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) =
          M₁.co.rho B.ψ z ((om₁ (1, h₁⁻¹) ∘ₗ e ∘ₗ om (1, m)) Φ)) ∧
        (∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), (om₁ (1, h₁⁻¹) ∘ₗ e ∘ₗ om (1, m)) (M.co.rho B.ψ u Φ) =
          (om₁ (1, h₁⁻¹) ∘ₗ e ∘ₗ om (1, m)) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he h₁ m hL
  have hs := IsUWeilPair.isUSplitting hP.weil
  have hs₁ := IsUWeilPair.isUSplitting hP₁.weil
  have hm1 : ∀ Φ ∈ schA F (Fin n × Fin d), om (1, m) Φ ∈ schA F (Fin n × Fin d) := fun Φ hΦ => hs.pres _ _ hΦ
  have hIm : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    simp [incM]
  have hinv : (mat h₁)ᵀ * (((h₁⁻¹ : UA σ W₁.J) : GL (Fin d₁) (AE F E)) : Matrix (Fin d₁) (Fin d₁) (AE F E))ᵀ = 1 := by
    have h0 : (((h₁⁻¹ : UA σ W₁.J) : GL (Fin d₁) (AE F E)) : Matrix (Fin d₁) (Fin d₁) (AE F E)) * mat h₁ = 1 := by
      show (((h₁⁻¹ * h₁ : UA σ W₁.J) : GL (Fin d₁) (AE F E)) : Matrix (Fin d₁) (Fin d₁) (AE F E)) = 1
      simp
    rw [← Matrix.transpose_mul, h0, Matrix.transpose_one]
  have vmv : ∀ (y : Fin n → AE F E) (v : Fin d → AE F E) (A : Matrix (Fin d) (Fin d) (AE F E)),
      Matrix.vecMulVec y v * Aᵀ = Matrix.vecMulVec y (A *ᵥ v) := by
    intro y v A
    ext i j
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
  refine ⟨fun Φ hΦ => ?_, fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_⟩
  · simp only [LinearMap.comp_apply]
    exact hs₁.pres _ _ (he.maps _ (hm1 Φ hΦ))
  · simp only [LinearMap.comp_apply]
    have h2 : actAB (cA σ) ((1 : UA σ X.J), m) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) =
        incM F (1 : Matrix (Fin n) (Fin n) E) * (z * (mat h₁)ᵀ) * (incM F H'.ι)ᵀ := by
      simp only [actAB, OneMemClass.coe_one, Units.val_one, hIm, Matrix.one_mul]
      change z * (incM F H'.ι)ᵀ * (mat m)ᵀ = _
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hL.2.2, Matrix.transpose_mul, Matrix.mul_assoc]
    have h3 : actAB (cA σ) ((1 : UA σ X.J), h₁⁻¹) (z * (mat h₁)ᵀ) = z := by
      simp only [actAB, OneMemClass.coe_one, Units.val_one, Matrix.one_mul]
      rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    rw [hs.impl _ _ _ hΦ, h2, he.Heisenberg₂ _ _ (hm1 Φ hΦ), hs₁.impl _ _ _ (he.maps _ (hm1 Φ hΦ)), h3]
  · obtain ⟨y, rfl⟩ := hu
    simp only [LinearMap.comp_apply]
    have hx : mat m *ᵥ incV F H'.x = incV F H'.x := by rw [hL.1]; simp
    have h4 : actAB (cA σ) ((1 : UA σ X.J), m) (Matrix.vecMulVec y (incV F H'.x)) = Matrix.vecMulVec y (incV F H'.x) := by
      simp only [actAB, OneMemClass.coe_one, Units.val_one, Matrix.one_mul]
      change Matrix.vecMulVec y (incV F H'.x) * (mat m)ᵀ = _
      rw [vmv, hx]
    rw [hs.impl _ _ _ hΦ, h4, he.inv _ ⟨y, rfl⟩ _ (hm1 Φ hΦ)]

end GlobalTheory.EvTwist

end
