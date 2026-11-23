import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussTop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VacKOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LawNbar

namespace PositivityTheory.Rg.Sw.Glob

theorem gaussian_law_of_weil (hW : WEx) (hF : FTfact) : GaussLaw :=
  gaussLaw_of' (vacK_of gZSch (lawN_of unipTau (tensInj_of awayIn))
    (lawNbar_of unipTau hW hF (tensInj_of awayIn) lNe) (locMul_of (tensInj_of awayIn)) lNe) gZSch

end PositivityTheory.Rg.Sw.Glob
