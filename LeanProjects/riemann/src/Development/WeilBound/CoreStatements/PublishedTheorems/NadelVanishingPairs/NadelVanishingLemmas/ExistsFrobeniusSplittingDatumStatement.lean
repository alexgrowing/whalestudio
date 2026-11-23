import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsFrobeniusSplittingDatum
open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.exists_frobenius_splitting_datum : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K), IsDatum p d f h → ∃ Φ, IsPhi p f h Φ := by
  first | exact @_root_.GlobalTheory.DI.exists_isPhi | exact _root_.GlobalTheory.DI.exists_isPhi | (intros; apply _root_.GlobalTheory.DI.exists_isPhi <;> assumption)
