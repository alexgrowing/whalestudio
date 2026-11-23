import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.MemOfInduces
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CbcCOfCbcc

namespace UpperTheory.Lit.Car

theorem dualR_of_wbc (hW : PositivityTheory.Pf1.CLGD.K.WBC) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hGK : GlobalTheory.Published.GelfandKazhdanDual)
    (hP : GlobalTheory.Published.GaloisRepOfPolarizedPair) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hJ : GlobalTheory.Published.JacquetShalikaRigidity) : DualR :=
  have hG := (bridge' hGK).2 hP
  ⟨lg_of (LocalGlobalAboveLAlt.local_global_compatibility_holds hW hG hB hL hJ) (LocalGlobalAboveLAlt.temperedness_transfer_holds hW hG hB hL hJ),
    csdSs_of hF hGK hG hB (LocalGlobalAboveLAlt.local_global_compatibility_holds hW hG hB hL hJ)⟩

theorem dualR_of_cbcc (hC : UpperTheory.V.Z.Bc.CBCc) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hGK : GlobalTheory.Published.GelfandKazhdanDual)
    (hP : GlobalTheory.Published.GaloisRepOfPolarizedPair) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hJ : GlobalTheory.Published.JacquetShalikaRigidity) : DualR :=
  dualR_of_wbc (UpperTheory.V.Z.Bc.wbc_of_cbcc hC) hF hGK hP hB hL hJ

end UpperTheory.Lit.Car
