import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesawStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneIntegralStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.MixXTorus

theorem evalZero_torus : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (t : (AE F E)ˣ) (m : UA σ X.J), IsLevi (W₁ := X₁) H t 1 m → ∀ Φ ∈ schA F (Fin n × Fin d),
        e (om (m, 1) Φ) = ((χW t : ℂ) * (((absE F E t : ℝ) ^ ((d : ℝ) / 2) : ℝ) : ℂ)) • e Φ := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he t m hL Φ hΦ
  have hs := IsUWeilPair.isUSplitting hP.weil
  have hm1 : mat m * incM F H.ι = incM F H.ι := by
    have := hL.2.2
    simpa [mat] using this
  have Heisenberg₂ : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), (e ∘ₗ om (m, 1)) (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) = M₁.co.rho B.ψ z ((e ∘ₗ om (m, 1)) Φ) := by
    intro z Φ hΦ
    simp only [LinearMap.comp_apply]
    rw [hs.impl _ _ _ hΦ]
    have hm2 : ((m : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F H.ι = incM F H.ι := hm1
    have : actAB (cA σ) (m, (1 : UA σ W.J)) (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) =
        incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ := by
      simp only [actAB, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc]
      rw [hm2]
    rw [this, he.Heisenberg₂ _ _ (hs.pres _ _ hΦ)]
  have hinv : ∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), (e ∘ₗ om (m, 1)) (M.co.rho B.ψ u Φ) = (e ∘ₗ om (m, 1)) Φ := by
    rintro u ⟨z, rfl⟩ Φ hΦ
    simp only [LinearMap.comp_apply]
    rw [hs.impl _ _ _ hΦ]
    have key : ∀ i, (∑ k, ((m : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) i k * incV F H.x k) = t.1 * incV F H.x i := by
      intro i
      have := congrFun hL.1 i
      simpa [mat, Matrix.mulVec, dotProduct] using this
    have hact : actAB (cA σ) (m, (1 : UA σ W.J)) (Matrix.vecMulVec (incV F H.x) z) = Matrix.vecMulVec (incV F H.x) (t.1 • z) := by
      simp only [actAB, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
      ext i j
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
      rw [show (∑ k, ((m : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) i k * (incV F H.x k * z j)) =
          (∑ k, ((m : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) i k * incV F H.x k) * z j by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring, key i]
      ring
    rw [hact]
    exact he.inv _ ⟨t.1 • z, rfl⟩ _ (hs.pres _ _ hΦ)
  have hadm : ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d), l ∘ₗ (e ∘ₗ om (m, 1)) ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro l hl
    have h1 := GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n₁ d X W X₁ W M M₁ H.ι 1 _ e hP.good hP₁.good he l hl
    exact hs.adm (m, 1) _ h1
  obtain ⟨c, hc⟩ := GlobalTheory.T.hermitian_adapted_plane_seesaw hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he
    (e ∘ₗ om (m, 1)) (fun Φ hΦ => he.maps _ (hs.pres _ _ hΦ)) Heisenberg₂ hinv hadm
  by_cases hne : ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0
  · rw [show e (om (m, 1) Φ) = c • e Φ from hc Φ hΦ, GlobalTheory.T.hermitian_adapted_plane_integral hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he t m hL c hc hne]
  · push_neg at hne
    have h0 := hne Φ hΦ
    rw [show e (om (m, 1) Φ) = c • e Φ from hc Φ hΦ, h0, smul_zero, smul_zero]

end GlobalTheory.MixXTorus
