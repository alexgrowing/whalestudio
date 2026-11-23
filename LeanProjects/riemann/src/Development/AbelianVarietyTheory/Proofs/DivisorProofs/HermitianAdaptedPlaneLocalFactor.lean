import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneVanishStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.MixXLeviU

theorem twist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (g₁ : UA σ X₁.J) (m : UA σ X.J), IsLevi H 1 g₁ m →
        (∀ Φ ∈ schA F (Fin n × Fin d), (om₁ (g₁⁻¹, 1) ∘ₗ e ∘ₗ om (m, 1)) Φ ∈ schA F (Fin n₁ × Fin d)) ∧
        (∀ z : Matrix (Fin n₁) (Fin d) (AE F E), ∀ Φ ∈ schA F (Fin n × Fin d),
          (om₁ (g₁⁻¹, 1) ∘ₗ e ∘ₗ om (m, 1)) (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) =
            M₁.co.rho B.ψ z ((om₁ (g₁⁻¹, 1) ∘ₗ e ∘ₗ om (m, 1)) Φ)) ∧
        (∀ u ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d),
          (om₁ (g₁⁻¹, 1) ∘ₗ e ∘ₗ om (m, 1)) (M.co.rho B.ψ u Φ) = (om₁ (g₁⁻¹, 1) ∘ₗ e ∘ₗ om (m, 1)) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he g₁ m hL
  have hs := hP.weil.isUSplitting
  have hs₁ := hP₁.weil.isUSplitting
  have hm1 : (((m, 1) : UA σ X.J × UA σ W.J).1 : GL (Fin n) (AE F E)).1 = mat m := rfl
  have h1 : ((((1 : UA σ W.J)) : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) = 1 := rfl
  refine ⟨fun Φ hΦ => ?_, fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_⟩
  · simp only [LinearMap.comp_apply]
    exact hs₁.pres _ _ (he.maps _ (hs.pres _ _ hΦ))
  · simp only [LinearMap.comp_apply]
    rw [hs.impl (m, 1) _ Φ hΦ]
    have ea : actAB (cA σ) ((m, 1) : UA σ X.J × UA σ W.J) (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) =
        incM F H.ι * (mat g₁ * z) * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ := by
      simp only [actAB]
      rw [h1, Matrix.transpose_one, Matrix.mul_one]
      have hL3 : ((m : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F H.ι = incM F H.ι * mat g₁ := hL.2.2
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hL3, Matrix.mul_assoc (incM F H.ι)]
    rw [ea, he.Heisenberg₂ (mat g₁ * z) _ (hs.pres _ _ hΦ), hs₁.impl (g₁⁻¹, 1) _ _ (he.maps _ (hs.pres _ _ hΦ))]
    congr 1
    simp only [actAB]
    rw [h1, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc]
    have hi : (((g₁⁻¹ : UA σ X₁.J) : GL (Fin n₁) (AE F E)) : Matrix (Fin n₁) (Fin n₁) (AE F E)) * mat g₁ = 1 := by
      rw [Subgroup.coe_inv]; exact Units.inv_mul _
    rw [hi, Matrix.one_mul]
  · obtain ⟨z', rfl⟩ := hu
    simp only [LinearMap.comp_apply]
    rw [hs.impl (m, 1) _ Φ hΦ]
    have ea : actAB (cA σ) ((m, 1) : UA σ X.J × UA σ W.J) (Matrix.vecMulVec (incV F H.x) z') = Matrix.vecMulVec (incV F H.x) z' := by
      simp only [actAB]
      rw [h1, Matrix.transpose_one, Matrix.mul_one]
      have hx : ((m : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ incV F H.x = incV F H.x := by
        rw [show ((m : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = mat m from rfl, hL.1]; simp
      conv_rhs => rw [← hx]
      ext i j
      simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
    rw [ea, he.inv _ ⟨z', rfl⟩ _ (hs.pres _ _ hΦ)]

theorem evalZero_levi_unit : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (g₁ : UA σ X₁.J) (m : UA σ X.J), IsLevi H 1 g₁ m → ∀ Φ ∈ schA F (Fin n × Fin d),
        e (om (m, 1) Φ) = om₁ (g₁, 1) (e Φ) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he
  refine GlobalTheory.T.hermitian_adapted_plane_vanish hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he ?_
  intro g₁ m hL
  obtain ⟨h1, h2, h3⟩ := twist F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he g₁ m hL
  have hs := hP.weil.isUSplitting
  have hs₁ := hP₁.weil.isUSplitting
  have hadm : ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d),
      l ∘ₗ (om₁ (g₁⁻¹, 1) ∘ₗ e ∘ₗ om (m, 1)) ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro l hl
    have a1 := hs₁.adm (g₁⁻¹, 1) l hl
    have a2 := GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n₁ d X W X₁ W M M₁ H.ι 1 _ e hP.good hP₁.good he _ a1
    exact hs.adm (m, 1) _ a2
  obtain ⟨c, hc⟩ := GlobalTheory.T.hermitian_adapted_plane_factor hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he _ h1 h2 h3 hadm
  refine ⟨c, fun Φ hΦ => ?_⟩
  have key := hc Φ hΦ
  have hinv : ∀ y, om₁ (g₁, 1) (om₁ (g₁⁻¹, 1) y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul,
      show ((g₁, 1) * (g₁⁻¹, 1) : UA σ X₁.J × UA σ W.J) = 1 from Prod.ext (mul_inv_cancel g₁) (mul_one _),
      map_one, Module.End.one_apply]
  calc e (om (m, 1) Φ) = om₁ (g₁, 1) (om₁ (g₁⁻¹, 1) (e (om (m, 1) Φ))) := (hinv _).symm
    _ = om₁ (g₁, 1) (c • e Φ) := by rw [← key]; rfl
    _ = c • om₁ (g₁, 1) (e Φ) := map_smul _ _ _

end GlobalTheory.MixXLeviU
