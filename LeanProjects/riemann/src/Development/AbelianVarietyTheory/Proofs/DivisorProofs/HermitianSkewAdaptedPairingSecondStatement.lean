import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSkewAdaptedPairingSecond
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtVecMulVecRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianSetAdditiveSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapPreservesRationalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDeterminantNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrAEMixedNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceOrth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumThreeComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensVmvLeft
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch GlobalTheory.ArchSchB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_skew_adapted_pairing_second : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁)
    (r s r' s' i₀ i₁ j₀ j₁ : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H.IsAdapted σ B X X₁ i₀ i₁ → H'.IsAdapted σ B W W₁ j₀ j₁ →
    ∀ (α : Fin d → AE F E) (c₁ : Fin n₁ → AE F E) (Z z' : Matrix (Fin n₁) (Fin d₁) (AE F E)),
    symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
      (Matrix.vecMulVec (incV F H.x) α + Matrix.vecMulVec (incM F H.ι *ᵥ c₁) (incV F H'.x) +
        incM F H.ι * Z * (incM F H'.ι)ᵀ) (incM F H.ι * z' * (incM F H'.ι)ᵀ) =
    symp (R := AF F) (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) Z z' := by
  first | exact @GlobalTheory.LeviPairing.pairing_eq | exact GlobalTheory.LeviPairing.pairing_eq | (intros; apply GlobalTheory.LeviPairing.pairing_eq <;> assumption)
