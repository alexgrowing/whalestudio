import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairFactorStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixWLeft

theorem twist_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ g : UA σ X.J,
        (∀ Φ ∈ schA F (Fin n × Fin d), (om₁ (g⁻¹, 1) ∘ₗ e ∘ₗ om (g, 1)) Φ ∈ schA F (Fin n × Fin d₁)) ∧
        (∀ z : Matrix (Fin n) (Fin d₁) (AE F E), ∀ Φ ∈ schA F (Fin n × Fin d), (om₁ (g⁻¹, 1) ∘ₗ e ∘ₗ om (g, 1)) (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) =
          M₁.co.rho B.ψ z ((om₁ (g⁻¹, 1) ∘ₗ e ∘ₗ om (g, 1)) Φ)) ∧
        (∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), (om₁ (g⁻¹, 1) ∘ₗ e ∘ₗ om (g, 1)) (M.co.rho B.ψ u Φ) =
          (om₁ (g⁻¹, 1) ∘ₗ e ∘ₗ om (g, 1)) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he g
  have hs := IsUWeilPair.isUSplitting hP.weil
  have hs₁ := IsUWeilPair.isUSplitting hP₁.weil
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    simp [incM]
  refine ⟨fun Φ hΦ => ?_, fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_⟩
  · exact hs₁.pres _ _ (he.maps _ (hs.pres _ _ hΦ))
  · simp only [LinearMap.comp_apply]
    rw [hs.impl (g, 1) _ Φ hΦ]
    have key : actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) =
        incM F (1 : Matrix (Fin n) (Fin n) E) * (mat g * z) * (incM F H'.ι)ᵀ := by
      simp [actAB, mat, h1, Matrix.mul_assoc]
    rw [key, he.Heisenberg₂ _ _ (hs.pres _ _ hΦ), hs₁.impl (g⁻¹, 1) _ _ (he.maps _ (hs.pres _ _ hΦ))]
    congr 2
    simp [actAB, mat, ← Matrix.mul_assoc]
  · obtain ⟨y, rfl⟩ := hu
    simp only [LinearMap.comp_apply]
    rw [hs.impl (g, 1) _ Φ hΦ]
    have key : actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) (Matrix.vecMulVec y (incV F H'.x)) =
        Matrix.vecMulVec (mat g *ᵥ y) (incV F H'.x) := by
      simp [actAB, mat, Matrix.mul_vecMulVec]
    rw [key, he.inv _ ⟨_, rfl⟩ _ (hs.pres _ _ hΦ)]

theorem evalZero_unitary_left : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ g, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) Φ) = om₁ (g, 1) (e Φ) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he
  refine GlobalTheory.T.skew_adapted_plane_pair_factor hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he ?_
  intro g
  obtain ⟨hmaps, hheis, hinv⟩ := twist_left F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he g
  have hspl := IsUWeilPair.isUSplitting hP.weil
  have hspl₁ := IsUWeilPair.isUSplitting hP₁.weil
  have hadm : ∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁),
      l ∘ₗ (om₁ (g⁻¹, 1) ∘ₗ e ∘ₗ om (g, 1)) ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro l hl
    have h1 := hspl₁.adm (g⁻¹, 1) l hl
    have h2 := GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he _ h1
    have h3 := hspl.adm (g, 1) _ h2
    simpa [LinearMap.comp_assoc] using h3
  obtain ⟨c, hc⟩ := GlobalTheory.T.skew_adapted_plane_pair_vanish hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he _ hmaps hheis hinv hadm
  refine ⟨c, fun Φ hΦ => ?_⟩
  have key := hc Φ hΦ
  have hinv1 : ∀ Ψ, om₁ (g, 1) (om₁ (g⁻¹, 1) Ψ) = Ψ := by
    intro Ψ
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  calc e (om (g, 1) Φ) = om₁ (g, 1) (om₁ (g⁻¹, 1) (e (om (g, 1) Φ))) := (hinv1 _).symm
    _ = om₁ (g, 1) ((om₁ (g⁻¹, 1) ∘ₗ e ∘ₗ om (g, 1)) Φ) := rfl
    _ = c • om₁ (g, 1) (e Φ) := by rw [key, map_smul]

end GlobalTheory.MixWLeft

end
