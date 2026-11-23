import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHeisenbergOperatorBoundedThetaFunction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_heisenbergOperatorBoundedThetaFunctions : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ), ∀ f : BBF σ JS JT ξ₀ ψ, Continuous fun w => rhoBF σ JS JT ξ₀ ψ hψ w f := by
  first | exact @GlobalTheory.RealWeilF.continuous_rhoBF | exact GlobalTheory.RealWeilF.continuous_rhoBF | (intros; apply GlobalTheory.RealWeilF.continuous_rhoBF <;> assumption)
