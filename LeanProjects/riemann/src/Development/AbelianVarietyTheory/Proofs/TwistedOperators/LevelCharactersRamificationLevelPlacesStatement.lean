import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacters_ramification_levelPlaces : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ (t : T0) (j : Fin D.R.m), Disjoint L.Pg (L.Q t) ∧ (∀ PP ∈ L.Q t, (L.C.mu0 j).UnrAt PP) ∧ (∀ PP ∈ L.Pg, (L.xiH t).UnrAt PP) ∧ ∀ PP', PP' ∉ L.Pg → (∀ PP ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → (L.C.mu0 j).UnrAt PP' := by
  first | exact @GlobalTheory.LevelRamif.ramif_at_levels | exact GlobalTheory.LevelRamif.ramif_at_levels | (intros; apply GlobalTheory.LevelRamif.ramif_at_levels <;> assumption)
