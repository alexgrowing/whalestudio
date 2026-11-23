import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevSph
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TopVol
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}
def datSph_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : LevDat (I.rec7 l Z).host.E ℂ (I.rec7 l Z).sp.X'.rank :=
  { datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) W.P.A3.A.μ0 with Q := ∅ }
def sphericalLevelSubgroup (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :=
  (Formalism.IndefR.Lev.levG _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.TopVol.datSph_alt W)).comap (MulAut.conj x⁻¹).toMonoidHom
def twistedLevelSubgroup (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (t : W.P.T) : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :=
  (Formalism.IndefR.Lev.levG _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)).comap (MulAut.conj x⁻¹).toMonoidHom
theorem mem_level_sphere_iff_conj_mem_levS {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X'} (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :
    h ∈ _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W x ↔ x⁻¹ * h * x ∈ levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.TopVol.datSph_alt W) := by
  simp [_root_.GlobalTheory.TopVol.sphericalLevelSubgroup, levS, MulAut.conj_apply]
theorem mem_level_twist_iff_conj_mem_levS_datXP {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X'} {t : W.P.T} (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :
    h ∈ _root_.GlobalTheory.TopVol.twistedLevelSubgroup W x t ↔ x⁻¹ * h * x ∈ levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) := by
  simp [_root_.GlobalTheory.TopVol.twistedLevelSubgroup, levS, MulAut.conj_apply]
end GlobalTheory.TopVol
end
end
