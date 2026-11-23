import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoin
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_reading_of_join : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), Join P → ∀ S : Reading P.T, IsTrue P S → RowUnit S → PairRead S := by
  first | exact @GlobalTheory.NPin.pairRead_of_join | exact GlobalTheory.NPin.pairRead_of_join | (intros; apply GlobalTheory.NPin.pairRead_of_join <;> assumption)
