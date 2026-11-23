import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactHighestWeightUniqueOfIrreducible
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactHighestWeight_unique_of_irreducible : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), KRel ε E → KUnit ε E → ∀ L : Submodule ℂ V, FiniteDimensional ℂ L → KStab ε E L → (∀ L' ≤ L, KStab ε E L' → L' = ⊥ ∨ L' = L) → ∀ (Λ : Fin n → ℝ) (v : V), v ∈ L → v ≠ 0 → KHighest ε E Λ v → (∀ ν : Fin n → ℝ, ∀ x ∈ L, x ≠ 0 → KHighest ε E ν x → ν = Λ) := by
  first | exact @GlobalTheory.HDUniq.khighest_weight_unique | exact GlobalTheory.HDUniq.khighest_weight_unique | (intros; apply GlobalTheory.HDUniq.khighest_weight_unique <;> assumption)
