import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryEigenIsotropicVectorLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalTorusFactorizationStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviLineAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem uAt_mul' {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} {g h : UA σ W.J}
    (hg : g ∈ UAt σ W (evFin F v)) (hh : h ∈ UAt σ W (evFin F v)) : g * h ∈ UAt σ W (evFin F v) := by
  intro u hu
  have e : mat (g * h) - 1 = mat g * (mat h - 1) + (mat g - 1) := by
    rw [show mat (g * h) = mat g * mat h from rfl, Matrix.mul_sub, Matrix.mul_one]; abel
  rw [e, smul_add, ← Matrix.mul_smul, hh u hu, hg u hu, Matrix.mul_zero, add_zero]

theorem uAt_inv' {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} {g : UA σ W.J}
    (hg : g ∈ UAt σ W (evFin F v)) : g⁻¹ ∈ UAt σ W (evFin F v) := by
  intro u hu
  have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by
    rw [Matrix.mul_sub, Matrix.mul_one, show mat g⁻¹ * mat g = 1 from Units.inv_mul g.1]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

theorem mul_inv_mem_unip {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    {t : (AE F E)ˣ} {h₁ : UA σ W₁.J} {m p : UA σ W.J} (hl : IsLevi H' t h₁ m)
    (hpx : mat p *ᵥ incV F H'.x = t.1 • incV F H'.x)
    (hpι : ∀ z, ∃ a : AE F E, mat p *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ (mat h₁ *ᵥ z) + a • incV F H'.x) :
    p * m⁻¹ ∈ unip σ W H' := by
  have hmi : mat m⁻¹ * mat m = 1 := Units.inv_mul m.1
  have hhi : mat h₁ * mat h₁⁻¹ = 1 := Units.mul_inv h₁.1
  have hmul : mat (p * m⁻¹) = mat p * mat m⁻¹ := rfl
  have hx : mat m⁻¹ *ᵥ incV F H'.x = (t⁻¹).1 • incV F H'.x := by
    calc mat m⁻¹ *ᵥ incV F H'.x = mat m⁻¹ *ᵥ ((t⁻¹).1 • (t.1 • incV F H'.x)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = (t⁻¹).1 • incV F H'.x := by
          rw [← hl.1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hmi, Matrix.one_mulVec]
  have hι : mat m⁻¹ * incM F H'.ι = incM F H'.ι * mat h₁⁻¹ := by
    calc mat m⁻¹ * incM F H'.ι = mat m⁻¹ * (incM F H'.ι * (mat h₁ * mat h₁⁻¹)) := by rw [hhi, Matrix.mul_one]
      _ = (mat m⁻¹ * mat m) * incM F H'.ι * mat h₁⁻¹ := by
          rw [← Matrix.mul_assoc (incM F H'.ι), ← hl.2.2]; simp only [Matrix.mul_assoc]
      _ = incM F H'.ι * mat h₁⁻¹ := by rw [hmi, Matrix.one_mul]
  refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
  · rw [hmul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul, hpx, smul_smul, Units.inv_mul, one_smul]
  · obtain ⟨a, ha⟩ := hpι (mat h₁⁻¹ *ᵥ z)
    refine ⟨a, ?_⟩
    rw [hmul, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z (mat m⁻¹) (incM F H'.ι), hι, ← Matrix.mulVec_mulVec, ha,
      Matrix.mulVec_mulVec z (mat h₁), hhi, Matrix.one_mulVec]

theorem levi_line_at : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ),
    B.IsGood σ → W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (v : Pl F) (p : UA σ W.J), p ∈ UAt σ W (evFin F v) → ∀ t : (AE F E)ˣ, mat p *ᵥ incV F H'.x = t.1 • incV F H'.x →
      ∃ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) ∧ ∃ (h₁ : UA σ W₁.J) (m : UA σ W.J),
        IsLevi H' t h₁ m ∧ m ∈ UAt σ W (evFin F v) ∧ h₁ ∈ UAt σ W₁ (evFin F v) ∧ p = u * m := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hA v p hp t hpx
  obtain ⟨ht, h₁, hh₁, hpι⟩ := GlobalTheory.T.unitary_eigen_isotropic_vector_local F E σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hA v p hp t hpx
  obtain ⟨m, hl, hm⟩ := GlobalTheory.T.unitary_local_torus_factorization F E σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hA v t ht h₁ hh₁
  exact ⟨p * m⁻¹, mul_inv_mem_unip hl hpx hpι, uAt_mul' hp (uAt_inv' hm), h₁, m, hl, hm, hh₁, by group⟩

end GlobalTheory.LeviLineAt
end
