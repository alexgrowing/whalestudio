import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleIntegralInterchange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_integral_interchange : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (S₁ S₂ : Type) [TopologicalSpace S₁] [SecondCountableTopology S₁]
    [MeasurableSpace S₁] [BorelSpace S₁] [TopologicalSpace S₂] [SecondCountableTopology S₂] [MeasurableSpace S₂] [BorelSpace S₂]
    (μ₁ : Measure S₁) (μ₂ : Measure S₂) [IsFiniteMeasure μ₁] (r : ℕ) (g : Fin r → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (f : Fin r → S₁ → S₂ → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
    (∀ j, g j ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) →
    (∀ j (T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ), Continuous (fun p : S₁ × S₂ => T (f j p.1 p.2))) →
    (∀ j (m n : ℕ), ∃ c : S₂ → ℝ, Continuous c ∧ Integrable c μ₂ ∧ ∀ s t, SchwartzMap.seminorm ℂ m n (f j s t) ≤ c t) →
    ∀ L ∈ (adeleClass F).adm κ,
      L (fun y => ∫ s, ∫ t, ∑ j, pureA F (f j s t) (g j) y ∂μ₂ ∂μ₁) = ∫ s, ∫ t, L (∑ j, pureA F (f j s t) (g j)) ∂μ₂ ∂μ₁ := by
  first | exact @GlobalTheory.AdmInt.adm_integral_comm | exact GlobalTheory.AdmInt.adm_integral_comm | (intros; apply GlobalTheory.AdmInt.adm_integral_comm <;> assumption)
