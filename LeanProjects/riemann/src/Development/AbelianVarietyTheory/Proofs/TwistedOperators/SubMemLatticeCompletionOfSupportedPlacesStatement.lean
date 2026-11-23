import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubMemLatticeCompletionOfSupportedPlaces
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLatti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_mem_lattice_completion_of_supported_places : ∀ (D : D7) (S : HSp D) (P : GlobalTheory.FinPl.Pl D → Prop) (L L' : GlobalTheory.FinPl.Lat S) (g : GA D S), g ∈ grpAt S P →
  (∀ y : Fin S.rank → AE D, y ∈ latV S L P → (mt S g - 1) *ᵥ y ∈ latV S L' P) →
  ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) L, (Lev.finE S g).1 *ᵥ x - x ∈ Formalism.L2.Herm.hatL (F := D.host.F) L' := by
  first | exact @GlobalTheory.LatBridge.sub_mem_hatL | exact GlobalTheory.LatBridge.sub_mem_hatL | (intros; apply GlobalTheory.LatBridge.sub_mem_hatL <;> assumption)
