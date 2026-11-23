import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTameFinitePlaceHermitian_all : ∀ (D : D7) (v : Pl D), Tame D v := by
  first | exact @GlobalTheory.FinPl.TamePlaces.tame | exact GlobalTheory.FinPl.TamePlaces.tame | (intros; apply GlobalTheory.FinPl.TamePlaces.tame <;> assumption)
