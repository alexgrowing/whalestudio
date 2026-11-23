import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.LocalToGlobal.GaloisLevelStructure.LinkHost
import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
import Formalism.LocalToGlobal.UnitaryNorms.CharGal
import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
import Formalism.LocalToGlobal.HermitianForms.TiedTwAll
import Formalism.LocalToGlobal.JointCharacters.SameChr
import Formalism.LocalToGlobal.HilbertRowConditions.KaTiedIffKapDef
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.NormalizedHeckeFactors.EMtLevel

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

structure LocalGlobalCompatibilityData (ex : Extra D L hT Gi Gl K Y cX) where

  host : Host.HostTied D

  level : Host.LevelTied D

  cols : Forms.ColsTied D

  full : Forms.ColsFull cols

  extra : Forms.ColumnsExtraCompatible full ex

  provA : TH.ProvA
  theta : Theta.AllTied D ex.th provA

  twIn : TwIn D
  n : NormalizedTwistCompatibility D ex.nch twIn

  frameN : Host.SameFrameN host n.gal.fr.jE

  thetaChr : Host.ThetaChrTied D n.cf ex.nch n.tp ex.th

  chrVal : Host.ValLL0 D n.cf

  chrDt : Host.DtTied D n.cf

  chrN : Host.NCharTied D n.cf ex.nch n.tp

  chrGal : Host.NGalChrTied D n.cf ex.nch n.tp

  chrPsi : Host.PsiChoiceCompatible D n.cf ex.nch n.tp

  tw : Forms.TwistedColumnsCompatible n.tp cols ex.tw

  sameChr : JoinChr.SameChr theta.T thetaChr

  what₂ : Rows.RowsCompatible D host n.cf n.tp

def Tied (ex : Extra D L hT Gi Gl K Y cX) : Prop := Nonempty (LocalGlobalCompatibilityData ex)

end

def C2 : FamClass := fun {_} Fm =>
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, Tied (Fm.ex x hx i)

end Formalism.L2
