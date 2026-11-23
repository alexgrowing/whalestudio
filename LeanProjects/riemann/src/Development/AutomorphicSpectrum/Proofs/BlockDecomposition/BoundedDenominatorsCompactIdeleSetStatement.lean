import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedDenominatorsCompactIdeleSet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_denominators_compact_idele_set : ∀ (F : Type) [Field F] [NumberField F] (D : Set (AF F)ˣ), IsCompact D → ∀ (S : Finset (HeightOneSpectrum (𝓞 F)))
    (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ v ∈ S, IsCompact (C v)) →
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ D, ∀ t : F, (∀ v ∈ S, algebraMap F (Fv F v) t * (u : AF F).2 v ∈ C v) →
      (∀ v, v ∉ S → algebraMap F (Fv F v) t * (u : AF F).2 v ∈ v.adicCompletionIntegers F) →
      ∃ y : 𝓞 F, (y : F) = N * t := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.Den.common_denominator | exact GlobalTheory.CompanionTheory.BasePsi.Den.common_denominator | (intros; apply GlobalTheory.CompanionTheory.BasePsi.Den.common_denominator <;> assumption)
