import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryEigenIsotropicVectorLocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_eigen_isotropic_vector_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ),
    B.IsGood σ → W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (v : Pl F) (p : UA σ W.J), p ∈ UAt σ W (evFin F v) → ∀ t : (AE F E)ˣ, mat p *ᵥ incV F H'.x = t.1 • incV F H'.x →
      At (F := F) (evFin F v) (t.1 - 1) ∧ ∃ h₁ : UA σ W₁.J, h₁ ∈ UAt σ W₁ (evFin F v) ∧
        ∀ z, ∃ a : AE F E, mat p *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ (mat h₁ *ᵥ z) + a • incV F H'.x := by
  first | exact @GlobalTheory.PlaneLeviBlock.levi_block | exact GlobalTheory.PlaneLeviBlock.levi_block | (intros; apply GlobalTheory.PlaneLeviBlock.levi_block <;> assumption)
