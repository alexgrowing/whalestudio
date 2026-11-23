import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEigenRankOneVecMulVec
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_eigen_rank_one_vecMulVec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W), IsStd B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W), H.IsAdapted σ B X X₁ j₀ j₁ →
    ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ (y : Fin d → AE F E) (u : Matrix (Fin d) (Fin n₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d),
      e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) y + incM F H.ι * uᵀ) Φ) = M₁.co.rho B.ψ uᵀ (e Φ) := by
  first | exact @GlobalTheory.LeviEvLaw.ev_law | exact GlobalTheory.LeviEvLaw.ev_law | (intros; apply GlobalTheory.LeviEvLaw.ev_law <;> assumption)
