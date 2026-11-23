import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtSame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideAAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvCg
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutomorphyOfMove
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrimitiveAtLinkedAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChoiceSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NdSpec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutSpec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Inner
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LabConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhtOn
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
end
section
variable {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C}
end
theorem Mv.exists_at_alt {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C} (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf C tp) :
    ∃ a' : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL m.D (m.cf cf) (m.ch C) (m.tp tp), _root_.GlobalTheory.LayerMove.AtSameAltAlt m a a' := by
  obtain ⟨⟨nb, pack⟩, all, chr_eq, host, frameN, chrN, chrGal, Pq', Pq_over, pq, jE_eq, mt_eq, Pq_eq, hlow, split, ratIn,
    r1, r2, r3, depth⟩ := a
  obtain ⟨D0, cf0, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C0, tp0, ch, mt, big, L, Sp, Au, ss, eq⟩ := nb
  subst eq
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at pack
  obtain ⟨rfl, rfl, rfl⟩ := pack
  have hmt : mtL L M = all.gal.mt := eq_of_heq mt_eq
  refine ⟨@_root_.GlobalTheory.Mem.Top.Bl.NAtData.mk hL m.D _ _ _
    (⟨@_root_.GlobalTheory.HeightCounting.NormChoiceConstructed.mk hL m.D m.pre.D (m.pre.cf cf0) jE (m.pre.sideA_alt A) ((_root_.UpperTheory.One.M.mvCg_alt trivial) m.pre cg) (m.pre.automorphy_of_move au) rep (m.pre.herm_wCell_last_mul_mulVec_eq_of_inWb row) low Pq S hk eig θ
      (m.pre.sideB_alt Bs) (m.pre.mt M) (m.pre.ch C0) (m.pre.tp tp0) (m.pre.choiceSide_alt ch) (m.pre.mtInput mt) big (m.pre.loc L)
      (m.pre.ndSpec_alt Sp) (m.pre.autSpec_alt Au) ((by with_unfolding_all exact (ss :))) m.withLoc_pre, m.pack_pre tp0⟩)
    ((_root_.UpperTheory.One.M.mvAll_alt trivial) m all)
    ((by with_unfolding_all exact ((congrArg (fun p : Σ c : CharFrame (withLoc L), TupTied (withLoc L) c (chL L C0) =>
      (⟨m.cf p.1, m.tp p.2⟩ : Σ c : CharFrame m.D, TupTied m.D c (m.ch (chL L C0)))) chr_eq) :)))
    (m.host host) ((by with_unfolding_all exact (frameN :))) (m.chrN chrN) (m.chrGal chrGal) ((by with_unfolding_all exact (Pq' :))) ((by with_unfolding_all exact (Pq_over :))) ((by with_unfolding_all exact (pq :))) ((by with_unfolding_all exact (jE_eq :)))
    ((by with_unfolding_all exact ((heq_of_eq (congrArg m.mt hmt)) :))) ((by with_unfolding_all exact (Pq_eq :))) ((by with_unfolding_all exact (hlow :))) (m.oSplit split) ((by with_unfolding_all exact ((m.pre.ratIn ratIn) :))) ((by with_unfolding_all exact (r1 :))) ((by with_unfolding_all exact (r2 :)))
    ((by with_unfolding_all exact (r3 :))) ((by with_unfolding_all exact ((m.pre.rowDepth depth) :))), ?_⟩
  refine ⟨HEq.rfl, (by with_unfolding_all exact ((HEq.refl Pq') :)), (by with_unfolding_all exact ((HEq.refl (ratL L S)) :)), (by with_unfolding_all exact ((HEq.refl hk) :)), (by with_unfolding_all exact ((HEq.refl rep) :)), (by with_unfolding_all exact ((HEq.refl eig) :)), ?_⟩
  rintro ⟨h1, h2, fr, h3, h4⟩
  exact ⟨(by with_unfolding_all exact ((m.pre.labConj_alt (A := A) h1) :)), (by with_unfolding_all exact (h2 :)), (by with_unfolding_all exact ((m.pre.omFrame fr) :)), (by with_unfolding_all exact (h3 :)), (by with_unfolding_all exact ((m.pre.phtOn_alt (A := A) h4) :))⟩
end GlobalTheory.LayerMove
end
end
