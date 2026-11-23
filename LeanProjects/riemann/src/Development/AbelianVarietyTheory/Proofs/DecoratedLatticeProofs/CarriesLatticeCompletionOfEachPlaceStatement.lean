import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfEachPlace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carriesLatticeCompletion_of_each_place : ∀ {D : D7} (S : HSp D) (g : GA D S) (L M : GlobalTheory.FinPl.Lat S) (Q : Finset (GlobalTheory.FinPl.Pl D)), (∀ v ∈ Q, GlobalTheory.FinPl.Moves S g L M (· = v)) → GlobalTheory.FinPl.Moves S g L M (· ∈ Q) := by
  first | exact @GlobalTheory.FinPl.MovesPl.moves_of_places | exact GlobalTheory.FinPl.MovesPl.moves_of_places | (intros; apply GlobalTheory.FinPl.MovesPl.moves_of_places <;> assumption)
