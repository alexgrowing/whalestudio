import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PMinusAnnihilatesLowestKTypeHolomorphicChamber
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
theorem _root_.GlobalTheory.T.pMinus_annihilates_lowestKType_holomorphicChamber : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ), GlRel E → IsUnitary ε E → StrictAnti lam → IsHolChamber ε lam → IsMin ε E lam → ∀ L : Submodule ℂ V, FiniteDimensional ℂ L → KStab ε E L → (∀ ν : Fin n → ℝ, ∀ x ∈ L, x ≠ 0 → KHighest ε E ν x → ν = lowK ε lam) → ∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ L, E b a x = 0 := by
  first | exact @GlobalTheory.HolDS.pMinus_kills_lowest | exact GlobalTheory.HolDS.pMinus_kills_lowest | (intros; apply GlobalTheory.HolDS.pMinus_kills_lowest <;> assumption)
