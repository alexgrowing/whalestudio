import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryBlockConjugate
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagColsZero

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_unitary_block_conjugate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' r₁ s₁ : ℕ),
    W.IsSkew σ B r' s' → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∃ (γ : UG (cA σ) (dbl (incM F W.J))) (S : Matrix (Fin 2 ⊕ Fin d₁) (Fin d) (AE F E))
      (S' : Matrix (Fin d) (Fin 2 ⊕ Fin d₁) (AE F E)),
      ((γ : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *
          (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
        GlobalTheory.DblSiegel.lagCols (incV F H'.x) (incM F H'.ι) * S ∧ S * S' = 1 ∧ S' * S = 1 := by
  first | exact @GlobalTheory.DblWitt.exists_unitary_diag_lag | exact GlobalTheory.DblWitt.exists_unitary_diag_lag | (intros; apply GlobalTheory.DblWitt.exists_unitary_diag_lag <;> assumption)
