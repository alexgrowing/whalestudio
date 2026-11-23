import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemImLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinatesInverse

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.UnipDom.LeviCoord

open Matrix GlobalTheory.ThK.UnipDom GlobalTheory.ThK.UnipDom.Inverse

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem fA_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : AE F E) (v w : Fin n → AE F E) :
    fA σ J v (s • w) = cA σ s * fA σ J v w := by
  have hc : (fun i => cA σ ((s • w) i)) = cA σ s • fun i => cA σ (w i) := by
    funext i; simp [map_mul]
  unfold fA
  rw [hc, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem fA_mat_iota {σ : E →ₐ[F] E} {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (H : Plane E d d₁) (g : UA σ J)
    (z : Fin d₁ → AE F E) :
    fA σ J (mat g *ᵥ (incM F H.ι *ᵥ z)) (incV F H.y) = coA σ J H g ⬝ᵥ z := by
  have key : ∀ z : Fin d₁ → AE F E, fA σ J (mat g *ᵥ (incM F H.ι *ᵥ z)) (incV F H.y) =
      ((incM F J *ᵥ fun i => cA σ (incV F H.y i)) ᵥ* (mat g * incM F H.ι)) ⬝ᵥ z := by
    intro z
    unfold fA
    rw [Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec]
  have hco : coA σ J H g = (incM F J *ᵥ fun i => cA σ (incV F H.y i)) ᵥ* (mat g * incM F H.ι) := by
    funext j
    simp only [coA]
    rw [key, dotProduct_single, mul_one]
  rw [key, hco]

theorem coA_coC_levi_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J) (h : UA σ G.V.J), IsLevi H l g₀ h → ∀ n : UA σ G.V.J,
    GlobalTheory.ThK.UnipDom.coA σ G.V.J H (h * n * h⁻¹) = l.1 • ((mat g₀⁻¹)ᵀ *ᵥ GlobalTheory.ThK.UnipDom.coA σ G.V.J H n) ∧
    GlobalTheory.ThK.UnipDom.coC σ G.V.J H (h * n * h⁻¹) = l.1 * cA σ l.1 * GlobalTheory.ThK.UnipDom.coC σ G.V.J H n := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' _ hB _ _ l g₀ h hL n
  have hσ := sigma_sigma hB.cm
  obtain ⟨-, hy, hι⟩ := hL
  have hyinv : mat h⁻¹ *ᵥ incV F H.y = cA σ l.1 • incV F H.y := by
    have e : mat h *ᵥ (cA σ l.1 • incV F H.y) = incV F H.y := by
      rw [Matrix.mulVec_smul, hy, smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul]
    conv_lhs => rw [← e]
    exact mat_inv_mulVec h _
  have hι' : mat h⁻¹ * incM F H.ι = incM F H.ι * mat g₀⁻¹ := by
    calc mat h⁻¹ * incM F H.ι = mat h⁻¹ * (incM F H.ι * mat g₀) * mat g₀⁻¹ := by
          simp only [Matrix.mul_assoc, ← mat_mul, mul_inv_cancel, mat_one, Matrix.mul_one]
      _ = mat h⁻¹ * (mat h * incM F H.ι) * mat g₀⁻¹ := by rw [hι]
      _ = incM F H.ι * mat g₀⁻¹ := by
          rw [← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mul]
  have hconj : ∀ v, mat h⁻¹ *ᵥ (mat (h * n * h⁻¹) *ᵥ v) = mat n *ᵥ (mat h⁻¹ *ᵥ v) := by
    intro v
    have e : h⁻¹ * (h * n * h⁻¹) = n * h⁻¹ := by group
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mat_mul, ← mat_mul, e]
  have hfA : ∀ v, fA σ G.V.J (mat (h * n * h⁻¹) *ᵥ v) (incV F H.y) =
      cA σ (cA σ l.1) * fA σ G.V.J (mat n *ᵥ (mat h⁻¹ *ᵥ v)) (incV F H.y) := by
    intro v
    rw [← fA_mulVec σ G.V.J h⁻¹, hconj, hyinv, fA_smul_right]
  have hl : cA σ (cA σ l.1) = l.1 := cA_cA hσ _
  refine ⟨?_, ?_⟩
  · funext j
    have e1 : coA σ G.V.J H (h * n * h⁻¹) j =
        fA σ G.V.J (mat (h * n * h⁻¹) *ᵥ (incM F H.ι *ᵥ Pi.single j 1)) (incV F H.y) := rfl
    rw [e1, hfA, hl, Matrix.mulVec_mulVec (M := mat h⁻¹), hι', ← Matrix.mulVec_mulVec, fA_mat_iota,
      Matrix.mulVec_single_one, Pi.smul_apply, smul_eq_mul, dotProduct_comm]
    rfl
  · have e2 : coC σ G.V.J H (h * n * h⁻¹) = fA σ G.V.J (mat (h * n * h⁻¹) *ᵥ incV F H.y) (incV F H.y) := rfl
    rw [e2, hfA, hl, hyinv, Matrix.mulVec_smul, fA_smul_left]
    show _ = l.1 * cA σ l.1 * fA σ G.V.J (mat n *ᵥ incV F H.y) (incV F H.y)
    ring

end GlobalTheory.ThK.UnipDom.LeviCoord

end
