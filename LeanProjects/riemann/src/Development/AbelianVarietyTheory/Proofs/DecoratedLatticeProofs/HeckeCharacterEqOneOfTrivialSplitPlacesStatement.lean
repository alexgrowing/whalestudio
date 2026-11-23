import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharacterEqOneOfTrivialSplitPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_eq_one_of_trivial_splitPlaces : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → (∀ e, IsSplitIdem D e → ∀ x : (AE D)ˣ, (e + cA D e) * ((x : AE D) - 1) = (x : AE D) - 1 → ν x = 1) → ∀ x, ν x = 1 := by
  first | exact @GlobalTheory.HeckeSplitAll.heckeChar_eq_one_of_split | exact GlobalTheory.HeckeSplitAll.heckeChar_eq_one_of_split | (intros; apply GlobalTheory.HeckeSplitAll.heckeChar_eq_one_of_split <;> assumption)
