import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
structure Parameters (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Type 2 where
  R : RPosition
  N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL
  S : SExt
  Γ : GeoP
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
@[reducible] def Parameters.s (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : Slots := ⟨p.R, _root_.GlobalTheory.Mem.Top.Bl.normChoiceOfExtension hL p.N, SXE p.S, OX p.Γ⟩
def WPt.core_data_of_point {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL q.x.what₂ q.x.n := q.x.nx.1
structure SpectralDataCompatible {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (S : _root_.Formalism.L2.TiedDataSAlt q.O.ex) : Prop where
  host : S.host = q.core_data_of_point.a.host
  cols : S.cols = q.x.col.C
  full : HEq S.full q.x.col.full
  g : HEq S.g q.x.col.g
  theta : (⟨S.provA, S.theta⟩ : Σ a, Formalism.L2.Theta.AllTied (q.w.D q.Z) q.O.ex.th a) = ⟨q.x.th.provA, q.x.th.all⟩
  twE : S.twIn.E = twEOf q.O.ex.xd
  twGood : DQ.GoodAllAt (q.w.D q.Z) q.O.ex.nch S.twIn
  chr : (⟨S.n.cf, S.n.tp⟩ : Σ c : CharFrame (q.w.D q.Z), TupTied (q.w.D q.Z) c q.O.ex.nch) = ⟨TC.cf q.w.I q.w.l q.Z, q.x.n.tp⟩
  gal : S.n.gal = q.core_data_of_point.a.all.gal
  nn : S.n.n = q.core_data_of_point.a.all.n
  exp : S.n.exp = q.core_data_of_point.a.all.exp
  chiD : S.n.chiD = q.core_data_of_point.a.all.chiD
  twF : S.n.twF = q.core_data_of_point.a.all.twF
  types : HEq S.n.types q.core_data_of_point.a.all.types
  cover : HEq S.n.cover q.core_data_of_point.a.all.cover
  plB : S.n.plB = q.core_data_of_point.a.all.plB
  thetaChr : HEq S.thetaChr q.x.th.chr
  dt : ∀ a, S.chrDt.eDt a = (QuotientGroup.mk a : GlobalTheory.Mem.Col2.DtQ q.B.host q.w.I.SQ)
  pieces : S.what₂.O.pieces.rcf = GlobalTheory.Mem.HD.qb S.host.fr.ι q.w.δ.ray ∧ S.what₂.O.pieces.MDel = GlobalTheory.Mem.HD.qb S.host.fr.ι q.w.δ.M'
  inK : S.inK = q.x.div.inK
  geo : HEq S.geo q.x.div.geo
  tw : ∃ he : q.O.ex.tw = q.w.tw q.Z, TC.StdTw q.w.I q.w.l q.Z q.w.l0 (he ▸ S.tw)
abbrev BoundaryReciprocity : GlobalTheory.Fc.BdT := fun _ O _ => _root_.Formalism.L2.RecTAlt O.ex
structure RecordCompatible {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex) : Prop where
  s : _root_.GlobalTheory.Mem.Top.Bl.SpectralDataCompatible q R.T.toTiedDataS
  k : KPin q R.T.ker
  crd : ∀ u i hi, R.T.crd u i hi = 1
variable {B : Base} {f : Fr B.toPre} {T : TwDat B}
structure RecordCompatibleExtended {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex) : Prop extends toRecPin : _root_.GlobalTheory.Mem.Top.Bl.RecordCompatible q R where
  entC : EntC q.x.ker
  std : GlobalTheory.Svd.StdAt q.w.I q.w.l q.w.l0 q.Z q.O R.T.ker
  rd : GlobalTheory.Pdv.StdRd q.w.I q.w.l q.Z R.T.ker
def ReciprocityLinkage (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : GlobalTheory.Fc.LkT _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity := linkOf (𝒮 := p.s) (Bd := _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity) fun _ q _ R => _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended (p := p) q R
@[reducible] def parametersOfExtension (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL := ⟨RX, N, S, Γ⟩
end GlobalTheory.Mem.Top.Bl
end
end
