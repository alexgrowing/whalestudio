import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatCongruenceLevel
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_congruence_level : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)),
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (a b : κ → AF F),
      (∀ k, evI F (a k) = 0 ∧ evI F (b k) = 0 ∧
        (∀ v, ∃ c ∈ v.adicCompletionIntegers F, evFin F v (a k) = (M₀ : Fv F v) * c) ∧
        (∀ v, ∃ c ∈ v.adicCompletionIntegers F, evFin F v (b k) = (M₀ : Fv F v) * c)) →
      schr ψ (a, b) (pureA F f g) = pureA F f g := by
  first | exact @GlobalTheory.SchrUnifDen.schr_fix_pure_uniform | exact GlobalTheory.SchrUnifDen.schr_fix_pure_uniform | (intros; apply GlobalTheory.SchrUnifDen.schr_fix_pure_uniform <;> assumption)
