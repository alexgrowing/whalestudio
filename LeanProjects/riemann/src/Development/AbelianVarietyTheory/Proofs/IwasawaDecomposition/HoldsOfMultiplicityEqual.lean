import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.OfDat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowPartNeBotPositiveDimension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsLOfCopy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoverFieldOfWeberLev
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LUnifAtDat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtDatLIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LargeCoefficientFieldContainsTwistValuesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspParamOfGreenParametrisationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLabelMapTwistCuspidalLabel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GreenSeriesIdempotentEqClassFunctionIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIoExtensionOfWeakCharacterisationFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.LiftsAt

open GlobalTheory.Mem.Top.GroupRetwisting

theorem serClause_of_typesTrue (hG : GlobalTheory.Published.GreenCuspidal) (D : D7) {P W} (h : TypesTrue D.ntypes P W) : SerClause D := by
  intro k
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hζ : Formalism.L2.NT.IsGenSys (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen := by
    intro d hd
    refine ⟨(GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_order d hd, fun d' hdd hd' => ?_⟩
    obtain ⟨e, rfl⟩ := hdd
    exact (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_norm d e hd (Nat.pos_of_mul_pos_left hd')
  obtain ⟨O, -, -, hO⟩ := GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel (ZMod (D.host.g k)) _
    (GlobalTheory.T.cuspParam_of_greenParametrisation hG (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k) _ hζ)
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  exact ⟨_, O, fun f => (h.ser k f).trans (GlobalTheory.T.greenSeriesIdempotent_eq_classFunctionIdempotent hG _ _ _ _ _ (h.teich k) O hO D.R.r f hr)⟩

def Closes (X : Stages) : Prop :=
  ∀ (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (Tw : TwDat X.B) (Wt : Set X.B.places.Pl) (z : Dat X I hX Tw Wt),
    TiesB z.R z.F → TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O → GlobalTheory.CuspMult.MultEq z.R.toRealDat → z.R.toRealDat.LIntegral →
      HoldsL z.R z.F

theorem ev_closes (P : Hypotheses3) (hRSW : GlobalTheory.Published.RegularisedSiegelWeilFirstTerm) (hHL : GlobalTheory.Published.HeckeLPartialContinuation) :
    Ev fun K => ∀ (X : Stages) (L : SizeData₂ X.toD7), L.sc = K.s → SizesAt L → Nonempty (ParameterChoice' X.toD7 L) → Closes X := by
  refine ⟨1, one_pos, fun eps _ h0 _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ?_⟩⟩⟩⟩
  obtain ⟨x₀, h⟩ := GlobalTheory.LiftsOnly.holdsL_of_ties P hRSW hHL eps h0
  exact ⟨x₀, fun K _ _ _ hs hx X L e hS hP px I hX Tw Wt z =>
    h z.core z.R z.F z.geo.κ z.geo.v₀ z.geo.O L (by rw [e]; exact hs) (by rw [e]; exact hx) hS hP⟩

set_option maxHeartbeats 2000000 in

theorem ties_at (hG : GlobalTheory.Published.GreenCuspidal) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok)
    (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (hN : GrpTrue Z.N f)
    (ok : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.Ok3 1) (hEx : z.R.toRealDat.ExAt)
    (host : Formalism.IndefR.Links.HostHyp (w.st Z).toD7) (par : ∃ L : SizeData₂ (w.st Z).toD7, Nonempty (ParameterChoice' (w.st Z).toD7 L))
    (hn : 8 * (w.st Z).toD7.R.f * (w.st Z).toD7.R.r + 4 ≤ (w.st Z).toD7.R.nV)
    (hI : IoExt z.R.toRealDat) (hU : z.R.toRealDat.LUnif) (hW : CoverAt.WeberLev B f T) :
    TiesB z.R z.F ∧ TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O := by
  have ty : TypesTrue (w.st Z).toD7.ntypes z.R.C.P z.R.C.W := by
    have e : z.R.toLevCh.C = Fr.at (w.st Z) f := z.lev.C.trans (congrArg (Fr.at (w.st Z)) w.C_eq)
    have e' : z.R.C = Fr.at (w.st Z) f := e
    rw [e']
    exact hN
  have hch := z.pins.char
  refine ⟨⟨ok, hch, hEx, host, par, B.ccK_top, z.pins.keep.guard,
    GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue hch.base.lev ty, serClause_of_typesTrue hG _ ty,
    GlobalTheory.Hk3.inertJunk_colIn3 _ _ _ hX _ _ _ _ _ _, z.pins.trSem, z.pins.keep.std, z.pins.phs, hn⟩,
    TiesG.of_dat z hU hI (fun i => ?_) (CoverAt.coverField_of_weberLev hW w Z hX Wt z)⟩
  exact GlobalTheory.OneMapRow3.oneFormMapRow_threeLevel_of_characterisation _ _ _ _ _ _ z.core z.R z.F z.geo.κ z.geo.v₀ z.geo.O (fun _ => 1) hn hch hEx ⟨z.geo.fw⟩ hI i
    (z.geo.pins i) (z.geo.phase i hU)

set_option maxHeartbeats 4000000 in

theorem holdsLU : Hypotheses3 → GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → GlobalTheory.Published.HeckeLPartialContinuation → (StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → GlobalTheory.CuspMult.MultEq z.R.toRealDat) → LowerUnitaryCaseCondition := by
  intro P hRSW hHL hM
  have hE : Step KPx (fun _ _ _ _ => True) fun K B f T => (∀ X : Stages, X.B = B →
      (∀ L : SizeData₂ X.toD7, L.sc = K.s → SizesAt L → Nonempty (ParameterChoice' X.toD7 L) → Closes X) ∧
      (X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) → (∀ w j, X.toD7.what₂.Aj j w = 0) →
        ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ SizesAt L ∧ Nonempty (ParameterChoice' X.toD7 L) ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) ∧
      Formalism.IndefR.Links.HostHyp X.toD7 ∧
      ∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧
        (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) :=
    Step.of_evG ((((evG_of_ev (ev_closes P hRSW hHL)).inter (evG_of_ev LedRec.ev_exists_sizeData)).inter
      (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)).imp fun K _ _ _ _ H B f T hO _ _ _ X e => by
        subst e
        exact ⟨H.1.1 X, H.1.2 X hO, (H.2 X hO).1, (H.2 X hO).2.2.2.2.2.2.1⟩)
  refine ((((hE.and (Step.of_evLgG (evLgG_of_evLg GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField))).and
    (Step.of_evLgG (q := fun _ => CoverAt.WeberLev) (evG_all CoverAt.lg_weberLev))).and hM).and
    (Step.and (lUnif_atDat P.q3 P.q2 P.q1) (atDat_lIntegral P.q3 P.q2 P.q1))).trans
    (Step.of_all fun K B f T _ _ _ H w hw Z hX Wt z g1 g2 hEx g4 => ?_)
  obtain ⟨⟨⟨⟨h1, hOk⟩, hW⟩, hM⟩, hU, hI⟩ := H
  obtain ⟨b, hb, heta, hA⟩ := LedRec.exists_bare P.q12 (C := w.C) Z f (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨hcl, hled, hhost, hV⟩ := h1 (w.st b) rfl
  obtain ⟨L, hL, hS, hP, hn⟩ := hled heta hA
  have s : SameGrp (C := w.C) Z b := LedRec.sameGrp g1 hb
  have hEx' := DatCopy.copy_exAt b s hEx
  have hU' := DatCopy.copy_lUnif b s (hU w hw Z hX Wt z g1 g2 hEx g4)
  have hT := ties_at P.q12 w b hX Wt (DatCopy.copy b s z) hb
    ((hOk w.px w.I hX w.ok w.C_eq w.xi_range).2 _ _ _ (DatCopy.copy b s z).good.irr) hEx' hhost ⟨L, hP⟩ hn
    (GlobalTheory.T.ioExt_of_weakCharacterisation_of_orthonormal_frames _ _ _ _ _ _ _ (DatCopy.copy b s z).R (DatCopy.copy b s z).F (DatCopy.copy b s z).pins.char hEx' hV) hU' hW
  exact LiftCopy.holdsL_of_copy b s (hcl L hL hS hP w.px w.I hX T Wt (DatCopy.copy b s z) hT.1 hT.2
    (DatCopy.copy_multEq b s (hM w hw Z hX Wt z g1 g2 hEx g4)) (DatCopy.copy_lIntegral b s (hI w hw Z hX Wt z g1 g2 hEx g4)))

end GlobalTheory.Mem.R3.LiftsAt

end
