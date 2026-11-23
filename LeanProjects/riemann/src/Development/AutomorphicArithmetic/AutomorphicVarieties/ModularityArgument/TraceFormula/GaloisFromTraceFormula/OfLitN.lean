import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeak
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.OfTempered
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem galWeak_of_litN (P : GlobalTheory.Mem.LiteralAutomorphy.LitN) (N : ℕ) : GalWeak N :=
  galWeak_of_cuspU (UpperTheory.GalN.weakG ((GlobalTheory.T.local_global_of_gelfand_kazhdan P.aut.gk).2 P.aut.gal))
    (GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein P.loc.llc P.loc.conv P.loc.dzc P.loc.dzi
      P.loc.brauer P.loc.chev P.aut.art P.loc.exh P.loc.multi P.loc.cos P.loc.zel P.loc.geo P.loc.bz) N

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula
