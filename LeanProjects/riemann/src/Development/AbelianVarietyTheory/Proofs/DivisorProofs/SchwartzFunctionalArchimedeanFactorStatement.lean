import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalArchimedeanFactor
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_functional_archimedean_factor : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (L : ((κ → AF F) → ℂ) → ℂ),
    (∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, L (Φ + Ψ) = L Φ + L Ψ) →
    (∀ (c : ℂ), ∀ Φ ∈ schA F κ, L (c • Φ) = c * L Φ) →
    (∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, L (pureA F f g) = T f) →
    (∀ a b : κ → F, ∀ Φ ∈ schA F κ,
      L (schr ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ) = L Φ) →
    ∃ c : ℂ, ∀ Φ ∈ schA F κ, L Φ = c * thetaSum F Φ := by
  first | exact @GlobalTheory.ThetaFunctionalUnique.main | exact GlobalTheory.ThetaFunctionalUnique.main | (intros; apply GlobalTheory.ThetaFunctionalUnique.main <;> assumption)
