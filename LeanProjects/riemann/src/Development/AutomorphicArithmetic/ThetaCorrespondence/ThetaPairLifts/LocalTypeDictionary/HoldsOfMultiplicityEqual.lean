import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsOfMultiplicityEqual
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HoldsLOfTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsOfMultiplicityEqualStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
namespace GlobalTheory.Mem.R3.LiftsAt
open GlobalTheory.Mem.Top.GroupRetwisting
theorem ev_closes_alt (P : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems) (hHL : GlobalTheory.Published.HeckeLPartialContinuation) :
    Ev fun K => ∀ (X : Stages) (L : SizeData₂ X.toD7), L.sc = K.s → SizesAt L → Nonempty (ParameterChoice' X.toD7 L) → Closes X := by
  refine ⟨1, one_pos, fun eps _ h0 _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ?_⟩⟩⟩⟩
  obtain ⟨x₀, h⟩ := _root_.GlobalTheory.LiftsOnly.holdsL_of_ties_alt P hHL eps h0
  exact ⟨x₀, fun K _ _ _ hs hx X L e hS hP px I hX Tw Wt z =>
    h z.core z.R z.F z.geo.κ z.geo.v₀ z.geo.O L (by rw [e]; exact hs) (by rw [e]; exact hx) hS hP⟩
set_option maxHeartbeats 4000000 in
theorem lu_of_multEq_at_data : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → (StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → GlobalTheory.CuspMult.MultEq z.R.toRealDat) → LowerUnitaryCaseCondition := by
  intro P hHL hM
  have hE : Step KPx (fun _ _ _ _ => True) fun K B f T => (∀ X : Stages, X.B = B →
      (∀ L : SizeData₂ X.toD7, L.sc = K.s → SizesAt L → Nonempty (ParameterChoice' X.toD7 L) → Closes X) ∧
      (X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) → (∀ w j, X.toD7.what₂.Aj j w = 0) →
        ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ SizesAt L ∧ Nonempty (ParameterChoice' X.toD7 L) ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) ∧
      Formalism.IndefR.Links.HostHyp X.toD7 ∧
      ∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧
        (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) :=
    Step.of_evG ((((evG_of_ev (_root_.GlobalTheory.Mem.R3.LiftsAt.ev_closes_alt P hHL)).inter (evG_of_ev LedRec.ev_exists_sizeData)).inter
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
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lu_of_multiplicity_equal : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → (StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → GlobalTheory.CuspMult.MultEq z.R.toRealDat) → LowerUnitaryCaseCondition := by
  first | exact @_root_.GlobalTheory.Mem.R3.LiftsAt.lu_of_multEq_at_data | exact _root_.GlobalTheory.Mem.R3.LiftsAt.lu_of_multEq_at_data | (intros; apply _root_.GlobalTheory.Mem.R3.LiftsAt.lu_of_multEq_at_data <;> assumption)
end
