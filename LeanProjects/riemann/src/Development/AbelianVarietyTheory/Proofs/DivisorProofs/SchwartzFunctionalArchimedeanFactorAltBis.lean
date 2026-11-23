import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqMulThetaSumCoset
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_functional_archimedean_factor_alt : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ L : ((κ → AF F) → ℂ) → ℂ, (∀ Ψ ∈ schA F κ, ∀ Ψ' ∈ schA F κ, L (Ψ + Ψ') = L Ψ + L Ψ') →
      (∀ c : ℂ, ∀ Ψ ∈ schA F κ, L (c • Ψ) = c * L Ψ) →
      (∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
        ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, L (pureA F f g) = T f) →
      (∀ ξ : κ → F, ∀ Ψ ∈ schA F κ, L (fun x => Ψ (x + fun i => algebraMap F (AF F) (ξ i))) = L Ψ) →
      (∀ z : κ → F, ∀ Ψ ∈ schA F κ, L (fun x => ψ (x ⬝ᵥ fun i => algebraMap F (AF F) (z i)) * Ψ x) = L Ψ) →
      ∀ a : F, a ≠ 0 → ∀ r : κ → FiniteAdeleRing (𝓞 F) F, ∃ c : ℂ,
        ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
          L (pureA F f (Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} fun _ => (1 : ℂ))) =
            c * thetaSum F (pureA F f (Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} fun _ => (1 : ℂ))) := by
  first | exact @GlobalTheory.CosetTheta.eq_mul_thetaSum_coset | exact GlobalTheory.CosetTheta.eq_mul_thetaSum_coset | (intros; apply GlobalTheory.CosetTheta.eq_mul_thetaSum_coset <;> assumption)
