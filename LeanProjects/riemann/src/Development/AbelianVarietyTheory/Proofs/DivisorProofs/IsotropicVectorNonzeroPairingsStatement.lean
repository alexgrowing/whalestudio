import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicVectorNonzeroPairings
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
theorem _root_.GlobalTheory.T.exists_isotropic_vector_pairing_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ x₀ x : Matrix (Fin n) (Fin 1) E, x₀ ≠ 0 → x ≠ 0 → Formalism.UG.cT (σ : E →+* E) x₀ * J * x₀ = 0 →
        Formalism.UG.cT (σ : E →+* E) x₀ * J * x = 0 →
        ∃ u : Matrix (Fin n) (Fin 1) E, Formalism.UG.cT (σ : E →+* E) u * J * u = 0 ∧
          Formalism.UG.cT (σ : E →+* E) x₀ * J * u ≠ 0 ∧ Formalism.UG.cT (σ : E →+* E) u * J * x ≠ 0 := by
  first | exact @GlobalTheory.exists_isotropic_vector_pairing_one | exact GlobalTheory.exists_isotropic_vector_pairing_one | (intros; apply GlobalTheory.exists_isotropic_vector_pairing_one <;> assumption)
