import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHighestVectorRealWeightUnitaryCompact
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
theorem _root_.GlobalTheory.T.exists_highest_vector_real_weight_unitary_compact : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), KRel ε E → KUnit ε E → ∀ N : Submodule ℂ V, FiniteDimensional ℂ N → KStab ε E N → N ≠ ⊥ → ∃ (μ : Fin n → ℝ) (w : V), w ∈ N ∧ w ≠ 0 ∧ KHighest ε E μ w := by
  first | exact @GlobalTheory.exists_kHighest_real_of_finiteDimensional | exact GlobalTheory.exists_kHighest_real_of_finiteDimensional | (intros; apply GlobalTheory.exists_kHighest_real_of_finiteDimensional <;> assumption)
