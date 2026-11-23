import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.DualRClosed
import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.FillOdd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp

namespace UpperTheory.Lit.Car

private theorem ll (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) : GlobalTheory.Published.LocalLanglandsGL :=
  GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein hN.loc.llc hN.loc.conv hN.loc.dzc hN.loc.dzi hN.loc.brauer hN.loc.chev
    hN.aut.art hN.loc.exh hN.loc.multi hN.loc.cos hN.loc.zel hN.loc.geo hN.loc.bz

theorem csdSs_litN (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) : UpperTheory.V.Lev.CsdSs :=
  (dualR_closed hN.aut.fin hN.aut.gk hN.aut.gal hN.aut.berger (ll hN) hN.aut.js.1).2

theorem csdMonoOdd_litN (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) : UpperTheory.V.Lev.CsdMonoOdd :=
  have hG := (bridge' hN.aut.gk).2 hN.aut.gal
  csdMonoOdd_of hN.aut.fin hN.aut.gk hG hN.aut.berger
    (LocalGlobalAboveLAlt.local_global_compatibility_holds (UpperTheory.V.Z.Bc.wbc_of_cbcc UpperTheory.ConvolutionTheory.cbcc) hG hN.aut.berger (ll hN) hN.aut.js.1)

end UpperTheory.Lit.Car
