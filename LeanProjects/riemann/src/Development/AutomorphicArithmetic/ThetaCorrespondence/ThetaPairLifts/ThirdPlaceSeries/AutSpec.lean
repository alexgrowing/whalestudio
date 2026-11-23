import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideAAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NdSpec
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
def Mv.autSpec_alt {big} {L : LocAll (lay0 D)} {Sp : NdSpec A.pl M C big L.X L.T} (x : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C) : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation (m.sideA_alt A) (m.mt M) (m.tp tp).tup (m.ndSpec_alt Sp).iq (m.loc L).Y (m.loc L).C := @_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (iotaQ := (by with_unfolding_all exact (x.iotaQ :)))
    (iotaQC := (by with_unfolding_all exact (x.iotaQC :)))
    (kFbar := (by with_unfolding_all exact (x.kFbar :)))
    (locW := (by with_unfolding_all exact (x.locW :)))
    (satW := (by with_unfolding_all exact (x.satW :)))
    (wdOf := (by with_unfolding_all exact (x.wdOf :)))
    (muC := (by with_unfolding_all exact (x.muC :)))
    (S := (by with_unfolding_all exact (x.S :)))
    (irr := (by with_unfolding_all exact (x.irr :)))
    (inj := (by with_unfolding_all exact (x.inj :)))
    (surj := (by with_unfolding_all exact (x.surj :)))
    (typeV := (by with_unfolding_all exact (x.typeV :)))
    (ptV := (by with_unfolding_all exact (x.ptV :)))
    (emb := (by with_unfolding_all exact (x.emb :)))
end
section
end
end GlobalTheory.LayerMove
end
end
