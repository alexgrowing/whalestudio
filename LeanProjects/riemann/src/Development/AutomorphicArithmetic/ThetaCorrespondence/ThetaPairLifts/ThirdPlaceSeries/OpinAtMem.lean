import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientDutyInPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.OPinAt
theorem mtInput_at_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp) : ∃ tup Q, MtInput D a.all.gal.mt tup Q := by
  have key : ∀ (D' : D7), D' = withLoc a.nt.L → ∀ M' : MtFam D', HEq (mtL a.nt.L a.nt.M) M' →
      ∃ tup Q, MtInput D' M' tup Q := by
    rintro _ rfl M' hM
    obtain rfl := eq_of_heq hM
    exact ⟨_, _, mtInput_mtL a.nt.L a.nt.M _ _ a.nt.mt⟩
  exact key D a.nt.eq _ a.mt_eq
theorem labTie_nt_of_labTie {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp)
    (h : GlobalTheory.SerSys.LabTie D fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) :
    GlobalTheory.SerSys.LabTie a.nt.D fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩ := by
  have key : ∀ (D' : D7), D' = withLoc a.nt.L →
      (GlobalTheory.SerSys.LabTie D' fun k => @GlobalTheory.Mem.TypePl.labDat (D'.host.g k) ⟨D'.host.g_prime k⟩) →
      GlobalTheory.SerSys.LabTie a.nt.D fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩ := by
    rintro _ rfl h'
    exact fun k => ⟨(h' k).1, (h' k).2⟩
  exact key D a.nt.eq h
end GlobalTheory.HeightCounting.Up.OPinAt
open GlobalTheory.HeightCounting.Up.OPinAt in
theorem GlobalTheory.HeightCounting.Up.oPin_at_mem : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => _root_.GlobalTheory.CoefDuty.OPinAlt c.a := by
  intro hL
  refine EvG.imp GlobalTheory.T.twistedPlace_innerProduct_classSum_rows fun K _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c hne _ hcp => ?_
  obtain ⟨m⟩ := hne
  have hs := H kp w hcp Z Wt t.hX t.r.z p0 t.r.Y t.r.intersectionNumber_baseChange t.exAt t.inGeo t.grp t.grpAt
  obtain ⟨tup, Q, hin⟩ := _root_.GlobalTheory.HeightCounting.Up.OPinAt.mtInput_at_alt c.a
  have hsum := hs c.a.all.gal.mt tup Q m.ad hin
  have hlab : GlobalTheory.SerSys.LabTie (w.D Z) fun k => @GlobalTheory.Mem.TypePl.labDat ((w.D Z).host.g k) ⟨(w.D Z).host.g_prime k⟩ :=
    fun k => ⟨(t.grp.teich k).symm, t.grp.ser k⟩
  exact
    { large := m.large
      inner := classSum_loc_of_sumTw hsum
      lab := _root_.GlobalTheory.HeightCounting.Up.OPinAt.labTie_nt_of_labTie c.a hlab
      gen := fun k => m.zeta k }
end
end
