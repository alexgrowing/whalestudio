import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermAdaptedEvaluationReduction
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
theorem _root_.GlobalTheory.T.herm_adapted_evaluation_reduction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d₁ : ℕ) (X : Spc F E n) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁) (r s n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ)
    (M₂ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ j₀ j₁ → ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁,
    IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → ∀ φ ∈ schA F (Fin n × Fin d₁),
    ∀ (w : Fin d₁ → E) (z : Fin d₁ → AE F E),
      thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) z) φ))) =
        B.ψ (-Algebra.trace (AF F) (AE F E) (GlobalTheory.UnipMass.hA σ W₁.J (incV F w) z)) *
          thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ)) := by
  first | exact @GlobalTheory.ThK.IsoPhaseComm.thetaSum_ev_phase | exact GlobalTheory.ThK.IsoPhaseComm.thetaSum_ev_phase | (intros; apply GlobalTheory.ThK.IsoPhaseComm.thetaSum_ev_phase <;> assumption)
