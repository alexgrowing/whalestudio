import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfEtSide
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Formal
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.FirstChernClassUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.EtaleMapFirstChern
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.FirstChernCompatGlue
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TiltSectionUnits.FcIsUnitSub
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TiltSectionUnits.NormLtOneOfMemMax
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.InWmTeichmullerSubOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FirstChernCompatibleL
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.LimitBilinearCup.LimOneExAlt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernCocycleAllLevels

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

theorem chapters_of (hP : BocksteinBaseChangeP) : Chapters where
  rin l _ := R.forE l
  et l _ K := E.etMap l K
  uniq := E.Main.firstChern_unique
  main l _ := B.main l
  compat l _ := B.compat l
  compatH l _ := B.compatH l
  c1 l _ := B.firstChern_compatible_l l
  p := hP

theorem etSideS (h4 : GlobalTheory.EtC.E4) (h8 : GlobalTheory.EtC.E8) : EtSideS := fun l _ K _ => (etSide (zIn formalIn h4 h8) l K).1

theorem cstSmooth_of_p (hP : BocksteinBaseChangeP) (h : EtSideS) : CstSmooth :=
  cstSmooth_of_etSide glueL glueE glueB factsC resEx h (chapters_of hP)

theorem crysPhiP_of_p (hP : BocksteinBaseChangeP) (hF : FSeamP) (h : EtSideS) : CrysPhiP :=
  glueP factsC h (chapters_of hP) (fun _ _ K ζ => HT.etMapP K ζ) hF

end CrystallineSemistableComparison
