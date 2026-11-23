import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerLeviDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeviElement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_stabilizer_levi_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ →
    W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : Pl F,
    ∀ p ∈ UAt σ W (evFin F v), ∀ a : AE F E, mat p *ᵥ incV F H'.x = a • incV F H'.x →
    ∃ (t : (AE F E)ˣ) (h₁ : UA σ W₁.J), (t : AE F E) = a ∧ At (evFin F v) ((t : AE F E) - 1) ∧
      h₁ ∈ UAt σ W₁ (evFin F v) ∧ ∀ z : Fin d₁ → AE F E, ∃ c : AE F E,
        mat p *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ (mat h₁ *ᵥ z) + c • incV F H'.x := by
  first | exact @GlobalTheory.ParabExtract.extract | exact GlobalTheory.ParabExtract.extract | (intros; apply GlobalTheory.ParabExtract.extract <;> assumption)
