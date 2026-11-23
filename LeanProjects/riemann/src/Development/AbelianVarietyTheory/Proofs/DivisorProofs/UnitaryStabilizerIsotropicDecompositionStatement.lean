import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStabilizerIsotropicDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_stabilizer_isotropic_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ →
    W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : Pl F,
    ∀ p ∈ UAt σ W (evFin F v), ∀ a : AE F E, mat p *ᵥ incV F H'.x = a • incV F H'.x →
    ∃ (n m : UA σ W.J) (t : (AE F E)ˣ) (h₁ : UA σ W₁.J), n ∈ unip σ W H' ∧
      n ∈ UAt σ W (evFin F v) ∧ m ∈ UAt σ W (evFin F v) ∧ h₁ ∈ UAt σ W₁ (evFin F v) ∧ IsLevi H' t h₁ m ∧
      p = n * m := by
  first | exact @GlobalTheory.PlaneParabolic.parabolic_decomp | exact GlobalTheory.PlaneParabolic.parabolic_decomp | (intros; apply GlobalTheory.PlaneParabolic.parabolic_decomp <;> assumption)
