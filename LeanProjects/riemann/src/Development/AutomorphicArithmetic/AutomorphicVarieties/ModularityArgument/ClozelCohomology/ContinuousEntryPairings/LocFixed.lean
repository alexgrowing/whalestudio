import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt

namespace GlobalTheory.ConjAut

open UpperTheory.V UpperTheory.V.Af

structure Tools : Prop where
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  descU : UpperTheory.V.Published.DescentUnitary
  sol : SolDescent
  galU : GalUnitary
  csdOf : CsdOf
  bridge : AutBridge
  algCyc : AlgOfCyc
  twi : Twi
  exC : ExC
  compat : CompatCsd
  iso : IsoOfFrob
  satFrob : SatFrob
  satLoc : SatLoc
  locC : LocCompC
  locFixed : LocFixed
  wdAway : WDAway
  satK : SatK
  levelK : LevelK
  pureK : PureK
  intK : IntK
  cardK : CardK
  levelP : UpperTheory.V.Br.LevelP
  pureP : UpperTheory.V.Br.PureP
  intP : UpperTheory.V.Br.IntP
  cardP : UpperTheory.V.Br.CardP

end GlobalTheory.ConjAut
