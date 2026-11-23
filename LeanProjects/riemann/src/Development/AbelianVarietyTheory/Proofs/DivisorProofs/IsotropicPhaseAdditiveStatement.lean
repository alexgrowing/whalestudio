import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPhaseAdditive
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_phase_additive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' : ℕ), IsCMExt F E σ → W.IsSkew σ B r' s' →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ w : Fin d₁ → E, ∀ u ∈ unip σ W H', ∀ v ∈ unip σ W H',
      GlobalTheory.IsoPhase.phase σ W H' w (u * v) = GlobalTheory.IsoPhase.phase σ W H' w u + GlobalTheory.IsoPhase.phase σ W H' w v := by
  first | exact @GlobalTheory.IsoPhaseAdd.phase_mul | exact GlobalTheory.IsoPhaseAdd.phase_mul | (intros; apply GlobalTheory.IsoPhaseAdd.phase_mul <;> assumption)
