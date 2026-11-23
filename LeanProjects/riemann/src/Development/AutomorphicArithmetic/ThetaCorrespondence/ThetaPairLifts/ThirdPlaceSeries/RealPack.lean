import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CxTiesOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx
  Formalism.IndefR.Links Formalism.L2.SG.PackageTie2 Formalism.L2.SG.KerJoinS Formalism.IndefR.CxPass
namespace GlobalTheory.MiS
open Formalism Formalism.IndefR Formalism.IndefR.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC}
structure RealPackAlt (ex : Extra D L hT Gi Gl Kc Yd cX) where
  R : _root_.Formalism.L2.RecTAlt ex
  S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R
  P : RowSideFamily ex
  Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)
  Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)
  Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3
  Ks : Type
  [fKs : Field Ks]
  [nKs : NumberField Ks]
  [aKs : Algebra Ks D.what₂.LL]
  Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks
attribute [instance] _root_.GlobalTheory.MiS.RealPackAlt.fKs _root_.GlobalTheory.MiS.RealPackAlt.nKs _root_.GlobalTheory.MiS.RealPackAlt.aKs
variable {ex : Extra D L hT Gi Gl Kc Yd cX}
def HypothesisAtPackage (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin W.R W.S W.Q) ∧
    (∀ u, Formalism.L2.SG.ColDict.LevelMatch W.S.X (W.S.tr u) W.S.Y.hK) ∧ DcPtG W.P ∧ W.Q.Rl.Char3 W.Q.F ∧ FramesOKg2 W.Q.Rl
abbrev packageCoefficientSpace (W : _root_.GlobalTheory.MiS.RealPackAlt ex) := W.Q.Rl.toCx3 W.Q.F
def LevelHypothesis (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  (∃ s, W.P.A3.fam3.Ok3 s) ∧ (_root_.GlobalTheory.MiS.packageCoefficientSpace W).RatZ ∧
    ∃ gE : Representation ℂ W.P.Gp (_root_.GlobalTheory.MiS.packageCoefficientSpace W).EE, GUnit3 (_root_.GlobalTheory.MiS.packageCoefficientSpace W) gE ∧ GEquiv3 W.P.A3 (_root_.GlobalTheory.MiS.packageCoefficientSpace W) gE ∧
      PrincipalLevelBijectivity W.P.A3 (_root_.GlobalTheory.MiS.packageCoefficientSpace W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) ∧
      LevType3 W.P.A3 (_root_.GlobalTheory.MiS.packageCoefficientSpace W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) gE false W.P.P0 W.P.ψ0 ∧
      LevType3 W.P.A3 (_root_.GlobalTheory.MiS.packageCoefficientSpace W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) gE true W.P.Ps W.P.ψs
end GlobalTheory.MiS
end
end
