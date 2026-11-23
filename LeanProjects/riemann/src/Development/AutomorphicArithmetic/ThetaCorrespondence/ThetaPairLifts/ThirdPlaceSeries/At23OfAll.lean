import Development.AutomorphicArithmetic.ResidueCharacters.ClosedOfAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyBoundAtTwoThreeOfLocalBounds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowTwo
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowThree
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
theorem at23_family_alt (hP : Hypotheses₂) {eps : ℝ} (Fm : FamP eps) : _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm :=
  _root_.UpperTheory.N.boundAtTwoThree_of_local_bounds_at_two_three three_ne_q (_root_.UpperTheory.N.exists_nonneg_twoC_constants_of_prints hP) (_root_.UpperTheory.N.exists_nonneg_threeC_constants_of_prints hP) Fm
theorem boundAtTwoThree_n_linked (h : ∀ {eps : ℝ} (Fm : FamP eps), _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) :
    _root_.GlobalTheory.Fc.RL.LinkedAt p (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm) :=
  _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (GlobalTheory.Fc.Row.of_sel fun _ _ _ => closed_of_all _ fun Fm _ => h Fm)
theorem boundAtTwoThree_linked_of_recT (hP : Hypotheses₂) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) :
    _root_.GlobalTheory.Fc.RL.LinkedAt p (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm) :=
  _root_.UpperTheory.N.boundAtTwoThree_n_linked (fun Fm => _root_.UpperTheory.N.at23_family_alt hP Fm) p
end UpperTheory.N
end
