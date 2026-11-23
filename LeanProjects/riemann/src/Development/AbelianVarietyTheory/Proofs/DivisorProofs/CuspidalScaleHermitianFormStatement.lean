import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalScaleHermitianForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_scale_hermitian_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J₀ J₁ : Matrix (Fin n) (Fin n) E) (k : E), k ≠ 0 → J₁ = k • J₀ →
    ∀ (φ₀ : GAd σ J₀ → ℂ) (φ₁ : GAd σ J₁ → ℂ), (∀ (g : GAd σ J₀) (g' : GAd σ J₁), g.1 = g'.1 → φ₁ g' = φ₀ g) →
      IsCuspidal σ J₀ φ₀ → IsCuspidal σ J₁ φ₁ := by
  first | exact @GlobalTheory.CuspScale.isCuspidal_smul | exact GlobalTheory.CuspScale.isCuspidal_smul | (intros; apply GlobalTheory.CuspScale.isCuspidal_smul <;> assumption)
