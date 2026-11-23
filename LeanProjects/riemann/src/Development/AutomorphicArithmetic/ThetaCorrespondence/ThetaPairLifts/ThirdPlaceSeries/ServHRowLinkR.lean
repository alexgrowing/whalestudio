import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReciprocityKernelService
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkRStdTie
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd
namespace GlobalTheory.Svd
theorem servH_row_linkR_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    Row (Bd := _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity) (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p) (ServH (Bd := _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity) fun _ _ _ R => R.T.ker) := by
  intro hA hL p
  exact GlobalTheory.T.bundle_bothParts_of_standardKernel_of_globalArtinReciprocity hA (Bd := _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity) (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p) (fun _ _ _ R => R.T.ker)
    (fun K X f T c h => (GlobalTheory.Svd.builtC_hasPart p.s).2 K X f T c
      (IsBuiltE.isBuilt K X f T c (IsGoodE.isBuiltE K X f T c h)))
    (_root_.GlobalTheory.Svd.LinkStd.linkR_stdTie_entry p (IsGoodE p.s))
end GlobalTheory.Svd
end
