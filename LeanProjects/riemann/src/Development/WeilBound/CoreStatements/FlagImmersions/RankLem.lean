import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MvPolynomialEqZeroOfEventually

namespace RootFieldNumerics

theorem rankLem : RankLem := fun _ _ _ _ hV hne hΦ hc =>
  GlobalTheory.CountableFibres.exists_injective_fderiv hV hne (fun z hz => (hΦ z hz).contDiffAt) hc

end RootFieldNumerics
