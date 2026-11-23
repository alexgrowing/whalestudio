import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesawStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneEigenStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixXUW

theorem evalZero_comm_U : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (h : UA σ W.J), ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, h) Φ) = om₁ (1, h) (e Φ) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he h Φ hΦ
  have hS := IsUWeilPair.isUSplitting hP.weil
  have hS₁ := IsUWeilPair.isUSplitting hP₁.weil
  have hone : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := by simp [incM]
  have hinv : om₁ (1, h) * om₁ (1, h⁻¹) = 1 := by rw [← map_mul, ← map_one om₁]; congr 1; ext <;> simp
  by_cases hz : ∀ Ψ ∈ schA F (Fin n × Fin d), e Ψ = 0
  · rw [hz _ (hS.pres _ _ hΦ), hz _ hΦ, map_zero]
  push_neg at hz
  set e' : Fn F n d →ₗ[ℂ] Fn F n₁ d := om₁ (1, h⁻¹) ∘ₗ e ∘ₗ om (1, h) with he'
  have e'_apply : ∀ Ψ, e' Ψ = om₁ (1, h⁻¹) (e (om (1, h) Ψ)) := fun Ψ => rfl
  have hmaps : ∀ Ψ ∈ schA F (Fin n × Fin d), e' Ψ ∈ schA F (Fin n₁ × Fin d) := fun Ψ hΨ =>
    hS₁.pres _ _ (he.maps _ (hS.pres _ _ hΨ))
  have hheis : ∀ z, ∀ Ψ ∈ schA F (Fin n × Fin d),
      e' (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Ψ) = M₁.co.rho B.ψ z (e' Ψ) := by
    intro z Ψ hΨ
    rw [e'_apply, e'_apply, hS.impl _ _ _ hΨ]
    have h1 : actAB (cA σ) ((1 : UA σ X.J), h) (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) =
        incM F H.ι * (z * (mat h)ᵀ) * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ := by
      simp only [actAB, hone, Matrix.transpose_one, Matrix.mul_one]
      simp [mat, Matrix.mul_assoc]
    rw [h1, he.Heisenberg₂ _ _ (hS.pres _ _ hΨ), hS₁.impl _ _ _ (he.maps _ (hS.pres _ _ hΨ))]
    congr 2
    simp only [actAB]
    have h2 : mat h⁻¹ * mat h = 1 := by
      show mat (h⁻¹ * h) = 1
      rw [inv_mul_cancel]; rfl
    show ((1 : Matrix (Fin n₁) (Fin n₁) (AE F E))) * (z * (mat h)ᵀ) * (mat h⁻¹)ᵀ = z
    rw [Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, h2, Matrix.transpose_one, Matrix.mul_one]
  have hinvI : ∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Ψ ∈ schA F (Fin n × Fin d),
      e' (M.co.rho B.ψ u Ψ) = e' Ψ := by
    rintro u ⟨z, rfl⟩ Ψ hΨ
    rw [e'_apply, e'_apply, hS.impl _ _ _ hΨ]
    have h1 : actAB (cA σ) ((1 : UA σ X.J), h) (Matrix.vecMulVec (incV F H.x) z) =
        Matrix.vecMulVec (incV F H.x) (mat h *ᵥ z) := by
      simp only [actAB]
      show (1 : Matrix (Fin n) (Fin n) (AE F E)) * Matrix.vecMulVec (incV F H.x) z * (mat h)ᵀ = _
      rw [Matrix.one_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    rw [h1, he.inv _ ⟨_, rfl⟩ _ (hS.pres _ _ hΨ)]
  have hadm : ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d), l ∘ₗ e' ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro l hl
    have a1 := hS₁.adm (1, h⁻¹) l hl
    have a2 := GlobalTheory.T.hermitian_adapted_plane_constant hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he _ a1
    have a3 := hS.adm (1, h) _ a2
    exact a3
  obtain ⟨c, hc⟩ := GlobalTheory.T.hermitian_adapted_plane_seesaw hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he e' hmaps hheis hinvI hadm
  have hc1 : c = 1 := GlobalTheory.T.hermitian_adapted_plane_eigen hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he h c
    (fun Ψ hΨ => hc Ψ hΨ) hz
  have key := hc Φ hΦ
  rw [hc1, one_smul, e'_apply] at key
  rw [← key, ← Module.End.mul_apply, hinv, Module.End.one_apply]

end GlobalTheory.MixXUW

end
