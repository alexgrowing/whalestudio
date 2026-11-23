import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalIsotropicFlagMovesStepIntoPrev
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_isotropicFlag_moves_step_into_prev : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r) (n : V ≃ₗ[E] V), n ∈ Fr.N → ∀ j : ℕ, j ≤ r → ∀ v ∈ Fr.Fj j, n v - v ∈ Fr.Fj (j - 1) ∧ n.symm v - v ∈ Fr.Fj (j - 1) := by
  first | exact @GlobalTheory.unipRadical_moves_step_into_prev | exact GlobalTheory.unipRadical_moves_step_into_prev | (intros; apply GlobalTheory.unipRadical_moves_step_into_prev <;> assumption)
