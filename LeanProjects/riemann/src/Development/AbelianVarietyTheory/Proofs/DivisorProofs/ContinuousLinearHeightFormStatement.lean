import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLinearHeightForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_linear_height_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (x x' : Fin n → E) (w : Fin d₁ → E), ∃ L : Matrix (Fin d) (Fin d) (AE F E) → AF F, Continuous L ∧
      ∀ (y : Fin d₁ → AE F E) (b : AE F E) (g : Matrix (Fin d) (Fin d) (AE F E)), incM F H'.ι *ᵥ y = g *ᵥ incV F H'.y - incV F H'.y - b • incV F H'.x →
        symp (cA σ) (-1 : AE F E) (incM F X.J) (incM F W₁.J) (Matrix.vecMulVec (incV F x') (incV F w)) (Matrix.vecMulVec (incV F x) y) = L g := by
  first | exact @GlobalTheory.ThK.IsoPhase.phase_continuous | exact GlobalTheory.ThK.IsoPhase.phase_continuous | (intros; apply GlobalTheory.ThK.IsoPhase.phase_continuous <;> assumption)
