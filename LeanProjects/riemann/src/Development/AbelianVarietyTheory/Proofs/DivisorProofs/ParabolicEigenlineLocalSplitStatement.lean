import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicEigenlineLocalSplit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_eigenline_local_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ),
    B.IsGood σ → W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (v : Pl F) (p : UA σ W.J), p ∈ UAt σ W (evFin F v) → ∀ t : (AE F E)ˣ, mat p *ᵥ incV F H'.x = t.1 • incV F H'.x →
      ∃ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) ∧ ∃ (h₁ : UA σ W₁.J) (m : UA σ W.J),
        IsLevi H' t h₁ m ∧ m ∈ UAt σ W (evFin F v) ∧ h₁ ∈ UAt σ W₁ (evFin F v) ∧ p = u * m := by
  first | exact @GlobalTheory.LeviLineAt.levi_line_at | exact GlobalTheory.LeviLineAt.levi_line_at | (intros; apply GlobalTheory.LeviLineAt.levi_line_at <;> assumption)
