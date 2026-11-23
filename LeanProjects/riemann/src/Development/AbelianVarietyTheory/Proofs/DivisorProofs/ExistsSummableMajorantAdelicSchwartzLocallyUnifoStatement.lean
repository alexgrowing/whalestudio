import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableMajorantAdelicSchwartzLocallyUnifo
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

open NumberField IsDedekindDomain
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_summableMajorant_adelicSchwartz_locallyUniform : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {P : Type} [TopologicalSpace P]
    (Ψ : P → (κ → AdeleRing (𝓞 F) F) → ℂ) (p0 : P) (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (f : P → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
    (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) →
    (∀ᶠ p in nhds p0, Ψ p = ∑ i, GlobalTheory.WeilM.pureA F (f p i) (g i)) →
    (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C) →
    ∀ x : κ → AdeleRing (𝓞 F) F, ∃ M : (κ → F) → ℝ, Summable M ∧
      ∀ᶠ p in nhds p0, ∀ ξ : κ → F, ‖Ψ p (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j)‖ ≤ M ξ := by
  first | exact @GlobalTheory.SchwartzMajorant.exists_summable_majorant | exact GlobalTheory.SchwartzMajorant.exists_summable_majorant | (intros; apply GlobalTheory.SchwartzMajorant.exists_summable_majorant <;> assumption)
