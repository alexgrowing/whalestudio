import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemLevSph
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QjPlaceNeLev

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl
namespace GlobalTheory.TopVol.InKConj
variable {D : D7}
end GlobalTheory.TopVol.InKConj
namespace GlobalTheory.TopVol.InKConj
theorem inK_mem_levSph_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ κ, InK (I.rec7 l Z).sp.X' a.v.NT (fun p => ∃ i, (J.G i).q.v = p) κ → κ ∈ _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat t J hJ κ hκ
  have hsd := W.Q.charW.base.lev.βX
  let row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t := fun t =>
    { vP := fun _ _ => 0, vT := fun _ _ _ => 0
      sBF := fun j ρ h => (GlobalTheory.Unf.Inhab.nonempty_stepBF W.Q.stdChar _ _).some
      sFB := fun j σ h => (GlobalTheory.Unf.Inhab.nonempty_stepFB W.Q.stdChar _ _).some
      io := fun _ => 0, ioT := fun _ _ => 0 }
  let col := fun t : W.P.T => (GlobalTheory.Fam.Check.colCh_nonempty (D := I.rec7 l Z) (u := u) ((I.rec7 l Z).chTw u (W.P.I.tup t))).choose
  have tie := (ha.tie row col).1
  have hNT : a.v.NT = a.g.LT := tie.bT.2
  have hm : ∀ v, (fun p => ∃ i, (J.G i).q.v = p) v → Moves _ a.g.bT (_root_.GlobalTheory.Fam.pk_z W).ΛX a.v.NT (· = v) := fun v _ => by
    rw [hNT]; exact tie.movesT _
  rw [_root_.GlobalTheory.TopVol.mem_level_sphere_iff_conj_mem_levS]
  exact conj_mem_levG _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.Fam.pk_z W).ΛX a.v.NT (_root_.GlobalTheory.TopVol.datSph_alt W) _ a.g.bT κ (hsd.elim fun _ h => h.1)
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ hsd) ha.top.2.1 hm rfl
    (fun PP hP ⟨i, hi⟩ => _root_.GlobalTheory.Fam.qj_place_ne_lev_alt W hW u a ha t J hJ i PP (Or.inr ((hW.lev.2.1 PP).1 hP)) hi) hκ
end GlobalTheory.TopVol.InKConj
end
