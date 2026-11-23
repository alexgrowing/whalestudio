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

namespace GlobalTheory.LeviNormUnip

open GlobalTheory.ThK.UnipDom.Inverse

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_mem_unipSet {σ : E →ₐ[F] E} {d d₁ : ℕ} {J : Matrix (Fin d) (Fin d) E} {H' : Plane E d d₁}
    (g : UA σ J) (c c' : AE F E) (M M' : Matrix (Fin d₁) (Fin d₁) (AE F E))
    (hx : mat g *ᵥ incV F H'.x = c • incV F H'.x) (hx' : mat g⁻¹ *ᵥ incV F H'.x = c' • incV F H'.x) (hcc : c' * c = 1)
    (hι : mat g * incM F H'.ι = incM F H'.ι * M) (hι' : mat g⁻¹ * incM F H'.ι = incM F H'.ι * M') (hMM : M * M' = 1)
    (u : UA σ J) (hu : u ∈ unipSet σ J H') : g * u * g⁻¹ ∈ unipSet σ J H' := by
  obtain ⟨hux, huz⟩ := hu
  refine ⟨?_, fun z => ?_⟩
  · rw [mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx', Matrix.mulVec_smul, hux,
      Matrix.mulVec_smul, hx, smul_smul, hcc, one_smul]
  · obtain ⟨a, ha⟩ := huz (M' *ᵥ z)
    refine ⟨a * c, ?_⟩
    have h1 : mat g⁻¹ *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ (M' *ᵥ z) := by
      rw [Matrix.mulVec_mulVec, hι', ← Matrix.mulVec_mulVec]
    have h2 : mat g *ᵥ (incM F H'.ι *ᵥ (M' *ᵥ z)) = incM F H'.ι *ᵥ z := by
      rw [Matrix.mulVec_mulVec, hι, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec (M := M), hMM, Matrix.one_mulVec]
    rw [mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, ha, Matrix.mulVec_add, h2,
      Matrix.mulVec_smul, hx, smul_smul]

theorem levi_conj_mem_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J) (h : UA σ G.V.J), IsLevi H l g₀ h →
    ∀ n ∈ unip σ G.V H, h * n * h⁻¹ ∈ unip σ G.V H ∧ h⁻¹ * n * h ∈ unip σ G.V H := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' _ _ _ _ l g₀ h hL n hn
  obtain ⟨hx, -, hι⟩ := hL
  have hn' := mem_unipSet hn
  have hx' : mat h⁻¹ *ᵥ incV F H.x = (l⁻¹).1 • incV F H.x := by
    have e := congrArg (fun v => (l⁻¹).1 • (mat h⁻¹ *ᵥ v)) hx
    simp only [mat_inv_mulVec, Matrix.mulVec_smul, smul_smul, Units.inv_mul, one_smul] at e
    exact e.symm
  have hι' : mat h⁻¹ * incM F H.ι = incM F H.ι * mat g₀⁻¹ := by
    have e : mat h⁻¹ * incM F H.ι * mat g₀ = incM F H.ι := by
      rw [Matrix.mul_assoc, ← hι, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mul]
    calc mat h⁻¹ * incM F H.ι = mat h⁻¹ * incM F H.ι * (mat g₀ * mat g₀⁻¹) := by
          rw [← mat_mul, mul_inv_cancel, mat_one, Matrix.mul_one]
      _ = incM F H.ι * mat g₀⁻¹ := by rw [← Matrix.mul_assoc, e]
  have hg : mat g₀ * mat g₀⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  have hg' : mat g₀⁻¹ * mat g₀ = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
  refine ⟨Subgroup.subset_closure (conj_mem_unipSet h l.1 (l⁻¹).1 _ _ hx hx' (Units.inv_mul l) hι hι' hg n hn'), ?_⟩
  have hm := conj_mem_unipSet (H' := H) h⁻¹ (l⁻¹).1 l.1 (mat g₀⁻¹) (mat g₀) hx' (by rw [inv_inv]; exact hx) (Units.mul_inv l)
    hι' (by rw [inv_inv]; exact hι) hg' n hn'
  rw [inv_inv] at hm
  exact Subgroup.subset_closure hm

end GlobalTheory.LeviNormUnip
