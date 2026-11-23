import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideAAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideB
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
theorem Mv.choiceSide_alt {low Pq S hk eig θ} {Bs : SideB D cf A.row low Pq S hk eig θ} (x : ChoiceSide D cf M Bs.exp C tp) : ChoiceSide m.D (m.cf cf) (m.mt M) (m.sideB_alt Bs).exp (m.ch C) (m.tp tp) := @_root_.GlobalTheory.HeightCounting.ChoiceSide.mk (_) (_) (_) (_) (_) (_)
    (nct := @_root_.Formalism.BasicNotions.NChTie.mk (_) (_)
      (twOf_eq := (by with_unfolding_all exact (x.nct.twOf_eq :)))
      (twSide_eq := (by with_unfolding_all exact (x.nct.twSide_eq :)))
      (Q_eq := (by with_unfolding_all exact (x.nct.Q_eq :)))
      (psi_eq := (by with_unfolding_all exact (x.nct.psi_eq :)))
      (embedding_baseField_condition := (by with_unfolding_all exact (x.nct.embedding_baseField_condition :))))
    (choice := @_root_.GlobalTheory.HeightCounting.ChoiceC.mk (_) (_)
      (twI_conj := (by with_unfolding_all exact (x.choice.twI_conj :)))
      (sd_place := (by with_unfolding_all exact (x.choice.sd_place :)))
      (emb_side := (by with_unfolding_all exact (x.choice.emb_side :)))
      (sd_conj := (by with_unfolding_all exact (x.choice.sd_conj :)))
      (one := (by with_unfolding_all exact (x.choice.one :)))
      (conj := (by with_unfolding_all exact (x.choice.conj :))))
    (off := (by with_unfolding_all exact (x.off :)))
    (adm := (by with_unfolding_all exact (x.adm :)))
    (psi := (by with_unfolding_all exact (x.psi :)))
    (eMt_level := (by with_unfolding_all exact (x.eMt_level :)))
end
section
end
end GlobalTheory.LayerMove
end
end
