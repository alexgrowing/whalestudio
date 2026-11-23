import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeServiceGlobalReciprocity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ServHRowLinkRStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowHServOfKerServ
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory
theorem row_hServ_of_link_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition),
    (∀ (K : Ctx) (β : BPt K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition β.D β.O c), Lk K β c b → _root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p K β c b.R) →
    _root_.GlobalTheory.Fc.R1.SlotServiceCondition (IsGoodE p.s) Lk := by
  intro hA hL p Lk hLk
  have h1 := Row.map (Bd := _root_.GlobalTheory.Fc.BundleCondition) (Q := IsGoodE p.s) (Lk := Lk) (Bd' := _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity) (Q' := IsGoodE p.s) (Lk' := _root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p)
    (fun _ _ _ b => b.R) (fun _ _ _ _ _ h => h) (fun K β c b _ h => hLk K β c b h) (_root_.GlobalTheory.T.reciprocity_kernel_of_artin hA p)
  exact _root_.GlobalTheory.Fc.R1.row_hServ_of_kerServ_alt _ Lk h1
end GlobalTheory
end
