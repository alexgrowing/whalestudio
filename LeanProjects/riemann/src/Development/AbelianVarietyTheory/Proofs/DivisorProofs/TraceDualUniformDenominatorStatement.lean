import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualUniformDenominator
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprime

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_dual_uniform_denominator : ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E) {n : ℕ} (A : Matrix (Fin n) (Fin n) E), A.det ≠ 0 →
    ∃ (m : ℕ) (β : Fin m → Fin n → 𝓞 E) (D : ℕ), D ≠ 0 ∧ ∀ ξ : Fin n → E,
      (∀ j, ∃ z : ℤ, Algebra.trace ℚ E (ξ ⬝ᵥ A *ᵥ fun i => σ (β j i)) = z) → ∀ i, ∃ o : 𝓞 E, (D : E) * ξ i = o := by
  first | exact @GlobalTheory.DenomTrace.integral_traces_bounded_denominators | exact GlobalTheory.DenomTrace.integral_traces_bounded_denominators | (intros; apply GlobalTheory.DenomTrace.integral_traces_bounded_denominators <;> assumption)
