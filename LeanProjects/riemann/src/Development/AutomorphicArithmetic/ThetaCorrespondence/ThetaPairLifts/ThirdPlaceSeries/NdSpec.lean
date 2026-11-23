import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideAAlt
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
def Mv.ndSpec_alt {big} {L : LocAll (lay0 D)} (x : NdSpec A.pl M C big L.X L.T) : NdSpec (m.sideA_alt A).pl (m.mt M) (m.ch C) big (m.loc L).X (m.loc L).T := @_root_.GlobalTheory.HeightCounting.NdSpec.mk (_) (_) (_) (_) (_) (_) (_)
    (iq := (by with_unfolding_all exact (x.iq :)))
    (iq_alg := (by with_unfolding_all exact (x.iq_alg :)))
    (iq_LL := (by with_unfolding_all exact (x.iq_LL :)))
    (iq_big := (by with_unfolding_all exact (x.iq_big :)))
    (B := @_root_.Formalism.L2.NLocBase.mk (_) (_)
      (Oc := (by with_unfolding_all exact (x.B.Oc :)))
      (ringOc := (by with_unfolding_all exact (x.B.ringOc :)))
      (domOc := (by with_unfolding_all exact (x.B.domOc :)))
      (dvrOc := (by with_unfolding_all exact (x.B.dvrOc :)))
      (ec := (by with_unfolding_all exact (x.B.ec :)))
      (ec_w := (by with_unfolding_all exact (x.B.ec_w :)))
      (V := (by with_unfolding_all exact (x.B.V :)))
      (acgV := (by with_unfolding_all exact (x.B.acgV :)))
      (modV := (by with_unfolding_all exact (x.B.modV :)))
      (modVO := (by with_unfolding_all exact (x.B.modVO :)))
      (towV := (by with_unfolding_all exact (x.B.towV :)))
      (iV := (by with_unfolding_all exact (x.B.iV :)))
      (iV_basis := (by with_unfolding_all exact (x.B.iV_basis :)))
      (Qc := (by with_unfolding_all exact (x.B.Qc :)))
      (hL := (by with_unfolding_all exact (x.B.hL :)))
      (hL_def := (by with_unfolding_all exact (x.B.hL_def :)))
      (hK := (by with_unfolding_all exact (x.B.hK :)))
      (hK_def := (by with_unfolding_all exact (x.B.hK_def :)))
      (split := (by with_unfolding_all exact (x.B.split :)))
      (Qc_over := (by with_unfolding_all exact (x.B.Qc_over :)))
      (Qc_conj := (by with_unfolding_all exact (x.B.Qc_conj :))))
    (Q_eq := (by with_unfolding_all exact (x.Q_eq :)))
    (mx := (by with_unfolding_all exact (x.mx :)))
    (mx_max := (by with_unfolding_all exact (x.mx_max :)))
    (mx_inj := (by with_unfolding_all exact (x.mx_inj :)))
    (mx_all := (by with_unfolding_all exact (x.mx_all :)))
    (phO := (by with_unfolding_all exact (x.phO :)))
    (phK := (by with_unfolding_all exact (x.phK :)))
    (phK_alg := (by with_unfolding_all exact (x.phK_alg :)))
    (phK_emb := (by with_unfolding_all exact (x.phK_emb :)))
    (Psi := (by with_unfolding_all exact (x.Psi :)))
    (Psi_inj := (by with_unfolding_all exact (x.Psi_inj :)))
    (Psi_range := (by with_unfolding_all exact (x.Psi_range :)))
    (Psi_pr := (by with_unfolding_all exact (x.Psi_pr :)))
    (ptX := (by with_unfolding_all exact (x.ptX :)))
    (ptX_hT := (by with_unfolding_all exact (x.ptX_hT :)))
    (iotaC := (by with_unfolding_all exact (x.iotaC :)))
    (iotaC_coh := (by with_unfolding_all exact (x.iotaC_coh :)))
    (Qc_eq := (by with_unfolding_all exact (x.Qc_eq :)))
    (std := (by with_unfolding_all exact (x.std :)))
    (act_hK := (by with_unfolding_all exact (x.act_hK :)))
    (twOf_eq := (by with_unfolding_all exact (x.twOf_eq :)))
    (twSide_eq := (by with_unfolding_all exact (x.twSide_eq :)))
    (psi_eq := (by with_unfolding_all exact (x.psi_eq :)))
    (twO_alg := (by with_unfolding_all exact (x.twO_alg :)))
    (tw_reads := (by with_unfolding_all exact (x.tw_reads :)))
    (heckeLoc_gamma_places := (by with_unfolding_all exact (x.heckeLoc_gamma_places :)))
    (nbr := (by with_unfolding_all exact (x.nbr :)))
    (nbr_ind := (by with_unfolding_all exact (x.nbr_ind :)))
    (self_good := (by with_unfolding_all exact (x.self_good :)))
    (nbr_iq := (by with_unfolding_all exact (x.nbr_iq :)))
    (bj := (by with_unfolding_all exact (x.bj :)))
    (bj_span := (by with_unfolding_all exact (x.bj_span :)))
    (bj_rel := (by with_unfolding_all exact (x.bj_rel :)))
end
section
end
end GlobalTheory.LayerMove
end
end
