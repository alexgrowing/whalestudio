import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermIsotropicVectors
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
theorem _root_.GlobalTheory.T.constant_term_isotropic_vectors : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g) →
      ∀ x₀ x : Matrix (Fin n) (Fin 1) E, x₀ ≠ 0 → Formalism.UG.cT (σ : E →+* E) x₀ * J * x₀ = 0 → x ≠ 0 →
        Formalism.UG.cT (σ : E →+* E) x * J * x = 0 → IsConstTerm σ J x₀ φ 0 → IsConstTerm σ J x φ 0 := by
  first | exact @GlobalTheory.WittLineCT.isConstTerm_zero_of_isConstTerm_zero | exact GlobalTheory.WittLineCT.isConstTerm_zero_of_isConstTerm_zero | (intros; apply GlobalTheory.WittLineCT.isConstTerm_zero_of_isConstTerm_zero <;> assumption)
