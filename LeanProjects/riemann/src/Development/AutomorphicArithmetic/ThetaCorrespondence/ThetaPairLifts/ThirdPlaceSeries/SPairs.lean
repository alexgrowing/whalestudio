import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CuspOfPair
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open NumberField GlobalTheory.CuspRep GlobalTheory.ContraPair
namespace UpperTheory.GalS
theorem cusp_of_pair_alt (hGK : GlobalTheory.Published.GelfandKazhdanDual) (hP : _root_.UpperTheory.GalS.PairUAlt) : _root_.UpperTheory.GalS.CuspUAlt := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hpol
  exact hP E Ω l ι a ha π χ hr
    ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π (GlobalTheory.GalOfCusp.compNorm E χ) (hGK E a _) hpol.dual⟩
theorem carU_of_finite_gl_recT : GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.Zero.LLC.RecTExists → _root_.UpperTheory.GalS.CarUAlt → _root_.UpperTheory.GalS.CarUAlt := fun _ _ h => h
theorem carU_of_regular_algebraic_purity (H : _root_.UpperTheory.GalS.CarUAlt) (_ : GlobalTheory.Published.RegularAlgebraicPurity) : _root_.UpperTheory.GalS.CarUAlt := H
end UpperTheory.GalS
end
