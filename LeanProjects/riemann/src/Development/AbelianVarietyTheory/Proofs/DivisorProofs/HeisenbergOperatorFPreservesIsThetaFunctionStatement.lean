import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFPreservesIsThetaFunction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperatorF_preserves_isThetaFunction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ),
    Continuous ψ → ∀ (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ), IsThetaFunOF σ JS JT ξ₀ ψ f →
      IsThetaFunOF σ JS JT ξ₀ ψ (heisOF σ JS JT ξ₀ ψ w₀ f) := by
  first | exact @GlobalTheory.HeisKeepF.isThetaFunOF_heisOF | exact GlobalTheory.HeisKeepF.isThetaFunOF_heisOF | (intros; apply GlobalTheory.HeisKeepF.isThetaFunOF_heisOF <;> assumption)
