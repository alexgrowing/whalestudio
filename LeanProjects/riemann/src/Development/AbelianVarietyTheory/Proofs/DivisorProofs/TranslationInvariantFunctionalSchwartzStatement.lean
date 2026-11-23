import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalSchwartz
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translation_invariant_functional_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : ((κ → AF F) → ℂ) → ℂ), (∀ Ψ ∈ schA F κ, ∀ Ψ' ∈ schA F κ, L (Ψ + Ψ') = L Ψ + L Ψ') →
      (∀ c : ℂ, ∀ Ψ ∈ schA F κ, L (c • Ψ) = c * L Ψ) →
      (∀ ξ : κ → F, ∀ Ψ ∈ schA F κ, L (fun x => Ψ (x + fun i => algebraMap F (AF F) (ξ i))) = L Ψ) →
      (∀ a : F, a ≠ 0 → ∀ r : κ → FiniteAdeleRing (𝓞 F) F, ∃ c : ℂ,
        ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
          L (pureA F f (Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} fun _ => (1 : ℂ))) =
            c * thetaSum F (pureA F f (Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} fun _ => (1 : ℂ)))) →
      ∃ c : ℂ, ∀ Ψ ∈ schA F κ, L Ψ = c * thetaSum F Ψ := by
  first | exact @GlobalTheory.ThetaGlue.main | exact GlobalTheory.ThetaGlue.main | (intros; apply GlobalTheory.ThetaGlue.main <;> assumption)
