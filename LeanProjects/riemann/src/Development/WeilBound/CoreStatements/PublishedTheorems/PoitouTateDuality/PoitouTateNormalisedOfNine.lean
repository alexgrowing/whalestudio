import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bridge
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.MemDecompositionSubgroupIff
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsHypOfCmp
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.VanishAll
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsShaFinal

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.PTN

theorem locHyp_holds : LocHyp := PositivityTheory.PTNLoc.locHyp

theorem poitouTateNormalised_of_ptfs (hfs : PtfsHyp) (hvan : VanishAll) :
    PoitouTateNormalised :=
  poitouTateNormalised_of hfs locHyp_holds hvan

theorem poitouTateNormalised_of_cmp (hN : PositivityTheory.Lit1.PTN.NineCmpFS) (hS : PositivityTheory.Lit1.PTN.ShaCmpFS) :
    PoitouTateNormalised :=
  poitouTateNormalised_of_ptfs (PositivityTheory.Lit1.PTN.ptfsHyp_of_cmp hN hS) PositivityTheory.Lit1.GFVanish.vanishAll

theorem poitouTateNormalised_of_nine (hN : PositivityTheory.Lit1.PTN.NineCmpFS) : PoitouTateNormalised :=
  poitouTateNormalised_of_cmp hN PositivityTheory.Lit1.PTN.shaCmpFS'

end PositivityTheory.PTN
