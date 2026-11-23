import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerFunctionalContinuous
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_functional_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ψ : AddChar (AF F) ℂ),
    IsStd ψ → ∀ (κ : Type) [Fintype κ], ∀ Λ ∈ (adeleClass F).adm κ, ∀ Φ ∈ schA F κ, ∀ (d : ℕ)
    (L : (Fin d → AE F E) →ₗ[AF F] (κ → AF F) × (κ → AF F)), Continuous fun u => Λ (schr ψ (L u) Φ) := by
  first | exact @GlobalTheory.DblSiegelX.continuous_admitted_schr_linear | exact GlobalTheory.DblSiegelX.continuous_admitted_schr_linear | (intros; apply GlobalTheory.DblSiegelX.continuous_admitted_schr_linear <;> assumption)
