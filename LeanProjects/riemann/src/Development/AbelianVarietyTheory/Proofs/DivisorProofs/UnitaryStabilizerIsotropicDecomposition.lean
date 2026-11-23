import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeviElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLeviDecompositionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerLeviDecompositionStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
noncomputable section
namespace GlobalTheory.PlaneParabolic
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

lemma mat_mul' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

lemma mat_one' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

lemma mat_inv_mul' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul', inv_mul_cancel, mat_one']

lemma mat_mul_inv' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul', mul_inv_cancel, mat_one']

lemma uAt_mul {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} {v : Pl F} {g h : UA σ X.J}
    (hg : g ∈ UAt σ X (evFin F v)) (hh : h ∈ UAt σ X (evFin F v)) : g * h ∈ UAt σ X (evFin F v) := by
  intro u hu
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    rw [mat_mul', Matrix.sub_mul, Matrix.one_mul]; abel
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

lemma uAt_inv {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} {v : Pl F} {g : UA σ X.J}
    (hg : g ∈ UAt σ X (evFin F v)) : g⁻¹ ∈ UAt σ X (evFin F v) := by
  intro u hu
  have e : mat g⁻¹ - 1 = -((mat g - 1) * mat g⁻¹) := by
    rw [Matrix.sub_mul, Matrix.one_mul, mat_mul_inv']; abel
  rw [e, smul_neg, ← Matrix.smul_mul, hg u hu, Matrix.zero_mul, neg_zero]

theorem parabolic_decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ →
    W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : Pl F,
    ∀ p ∈ UAt σ W (evFin F v), ∀ a : AE F E, mat p *ᵥ incV F H'.x = a • incV F H'.x →
    ∃ (n m : UA σ W.J) (t : (AE F E)ˣ) (h₁ : UA σ W₁.J), n ∈ unip σ W H' ∧
      n ∈ UAt σ W (evFin F v) ∧ m ∈ UAt σ W (evFin F v) ∧ h₁ ∈ UAt σ W₁ (evFin F v) ∧ IsLevi H' t h₁ m ∧
      p = n * m := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hA v p hp a hpa
  obtain ⟨t, h₁, hta, htv, hh₁, hι⟩ := GlobalTheory.T.local_stabilizer_levi_decomposition F E σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hA v p hp a hpa
  obtain ⟨m, hL, hm⟩ := GlobalTheory.T.local_levi_decomposition_exists F E σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hA v t h₁ htv hh₁
  have hmx : mat m⁻¹ *ᵥ incV F H'.x = (t⁻¹ : (AE F E)ˣ).1 • incV F H'.x := by
    have h1 : mat m⁻¹ *ᵥ ((t : AE F E) • incV F H'.x) = incV F H'.x := by
      rw [← hL.1, Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
    rw [Matrix.mulVec_smul] at h1
    have h3 : mat m⁻¹ *ᵥ incV F H'.x = (t⁻¹ : (AE F E)ˣ).1 • ((t : AE F E) • (mat m⁻¹ *ᵥ incV F H'.x)) := by
      rw [smul_smul, Units.inv_mul, one_smul]
    rw [h3, h1]
  have hmι : ∀ z, mat m⁻¹ *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ (mat h₁⁻¹ *ᵥ z) := by
    intro z
    have h2 : mat m⁻¹ * incM F H'.ι = incM F H'.ι * mat h₁⁻¹ := by
      calc mat m⁻¹ * incM F H'.ι = mat m⁻¹ * (incM F H'.ι * mat h₁) * mat h₁⁻¹ := by
            simp only [Matrix.mul_assoc, mat_mul_inv', Matrix.mul_one]
        _ = incM F H'.ι * mat h₁⁻¹ := by
            rw [← hL.2.2]; simp only [← Matrix.mul_assoc, mat_inv_mul', Matrix.one_mul]
    rw [Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec]
  refine ⟨p * m⁻¹, m, t, h₁, Subgroup.subset_closure ⟨?_, fun z => ?_⟩, uAt_mul hp (uAt_inv hm), hm, hh₁, hL, by group⟩
  · rw [mat_mul', ← Matrix.mulVec_mulVec, hmx, Matrix.mulVec_smul, hpa, smul_smul, ← hta, Units.inv_mul, one_smul]
  · obtain ⟨c, hc⟩ := hι (mat h₁⁻¹ *ᵥ z)
    refine ⟨c, ?_⟩
    have h4 : mat h₁ *ᵥ (mat h₁⁻¹ *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, mat_mul_inv', Matrix.one_mulVec]
    rw [mat_mul', ← Matrix.mulVec_mulVec, hmι, hc, h4]

end GlobalTheory.PlaneParabolic
