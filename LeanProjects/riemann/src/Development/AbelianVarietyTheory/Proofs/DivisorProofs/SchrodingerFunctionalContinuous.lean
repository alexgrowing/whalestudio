import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralBound

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.DblSiegelX

theorem continuous_admitted_schr_linear : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ψ : AddChar (AF F) ℂ),
    IsStd ψ → ∀ (κ : Type) [Fintype κ], ∀ Λ ∈ (adeleClass F).adm κ, ∀ Φ ∈ schA F κ, ∀ (d : ℕ)
    (L : (Fin d → AE F E) →ₗ[AF F] (κ → AF F) × (κ → AF F)), Continuous fun u => Λ (schr ψ (L u) Φ) := by
  intro F E _ _ _ _ _ ψ hψ κ _ Λ hΛ Φ hΦ d L
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hL : Continuous L := IsModuleTopology.continuous_of_linearMap L
  exact (GlobalTheory.ConeMeasSmall.continuous_schr hψ hΛ hΦ).comp hL

end GlobalTheory.DblSiegelX
