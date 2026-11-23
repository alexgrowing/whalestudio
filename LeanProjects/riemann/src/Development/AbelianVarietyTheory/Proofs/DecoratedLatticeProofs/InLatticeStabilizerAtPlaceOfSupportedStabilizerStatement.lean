import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlaceOfSupportedStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inLatticeStabilizerAtPlace_of_supportedStabilizer : ∀ (D : D7) (S : HSp D) (L : Lat S) (v : Pl D) (κ : GA D S), IsSelfDualC S L → InK S L (· = v) κ → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.InStabAt S L v κ := by
  first | exact @GlobalTheory.KStabBridge.inStabAt_of_inK | exact GlobalTheory.KStabBridge.inStabAt_of_inK | (intros; apply GlobalTheory.KStabBridge.inStabAt_of_inK <;> assumption)
