import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinkRStdTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BuiltCHasPart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BundleBothPartsOfStandardKernelOfGlobalArtinReciStatement
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd

namespace GlobalTheory.Svd

theorem servH_row_linkR : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL),
    Row (Bd := BdRec) (IsGoodE p.s) (LinkR p) (ServH (Bd := BdRec) fun _ _ _ R => R.T.ker) := by
  intro hA hL p
  exact GlobalTheory.T.bundle_bothParts_of_standardKernel_of_globalArtinReciprocity hA (Bd := BdRec) (IsGoodE p.s) (LinkR p) (fun _ _ _ R => R.T.ker)
    (fun K X f T c h => (GlobalTheory.Svd.builtC_hasPart p.s).2 K X f T c
      (IsBuiltE.isBuilt K X f T c (IsGoodE.isBuiltE K X f T c h)))
    (GlobalTheory.Svd.LinkStd.linkR_stdTie p (IsGoodE p.s))

end GlobalTheory.Svd
