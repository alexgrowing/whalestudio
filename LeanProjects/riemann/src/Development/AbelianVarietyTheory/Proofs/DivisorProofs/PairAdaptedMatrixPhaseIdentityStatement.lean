import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedMatrixPhaseIdentity
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIncMLagP

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_adapted_matrix_phase_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (Z Z' : Matrix (Fin d₁) (Fin n) (AE F E)) (Y Y' : Fin n ⊕ Fin n → AE F E),
      symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))
        (incM F H'.ι * (Z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) + Matrix.vecMulVec (incV F H'.x) Y)
        (incM F H'.ι * (Z' * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) + Matrix.vecMulVec (incV F H'.x) Y') = 0 := by
  first | exact @GlobalTheory.SiegelIsotr.isotropic_mixed | exact GlobalTheory.SiegelIsotr.isotropic_mixed | (intros; apply GlobalTheory.SiegelIsotr.isotropic_mixed <;> assumption)
