import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TupAllUsedAtPart
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricWeakTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefiniteSideCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowRRowsOfParts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWPRowsOfRowsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallAlongStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacementOfRealisationStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoAtChosenStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventualL6OfLowerScalarStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.StageZeroRow
theorem tupAllUsed_at_part_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : Formalism.L2.DIV.TupAllUsed b.P := by
  intro t
  rcases b.pt.charW.tup.mu_used t with h | ⟨w, hw⟩
  · left
    subst h
    exact b.P.tied.div.tup.mu0
  · right
    refine ⟨D.plEq.symm w, ?_⟩
    have e1 := b.pt.tupAt (D.plEq.symm w)
    rw [Equiv.apply_symm_apply] at e1
    have e2 := b.pt.tupTie (D.what₂.muAt (D.plEq.symm w)) (Or.inr ⟨_, rfl⟩)
    rw [e1, hw] at e2
    exact e2
theorem p_div_at_piece_of_div3g {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) (h : GlobalTheory.Cp.DivRows3G b.P) : _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b :=
  Formalism.L2.DIV.DivRows3G.toRows (_root_.GlobalTheory.Fc.StageZeroRow.tupAllUsed_at_part_alt b)
    ⟨h.sharpRR, h.baseRR, h.divisionRows_rationalLift, h.thTheta, ⟨h.num.Ij, h.num.jw, h.num.etaJ⟩, h.colsBk⟩
theorem row_rRows_stage0_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.DiscreteSeriesClassification → _root_.GlobalTheory.BigOn.SurjectiveOntoX → _root_.GlobalTheory.BigTop.LambdaLowerBound₂ → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition Q Lk → _root_.GlobalTheory.Fc.R1.SlotDivisorCondition Q Lk → _root_.GlobalTheory.Fc.RL.RowGoodnessCondition Q Lk → _root_.GlobalTheory.Fc.S0.GeometricWeakCompatibility' Q Lk → _root_.GlobalTheory.Fc.S0.CovolumeBoundThirdPlaceSeries Q Lk → _root_.GlobalTheory.Fc.S0.FunctionalCondition Q Lk → _root_.GlobalTheory.Fc.RL.RowMultiplicityCondition Q Lk → _root_.GlobalTheory.Fc.RL.RowKappaCondition Q Lk → _root_.GlobalTheory.Fc.RL.RowDefectCondition Q Lk → _root_.GlobalTheory.Fc.R1.SlotDefiniteRowsCondition _root_.GlobalTheory.Fc.DefiniteSideCondition Q Lk := by
  intro hDS hHC hCR hCW hDC hOnto hLam Q Lk hPA hDiv hGood hGeo hL3 hFun hMi hKap hDf
  refine _root_.GlobalTheory.Fc.row_rRows_of_parts_alt _root_.GlobalTheory.Fc.DefiniteSideCondition Q Lk ?_ hMi hKap hDf
  refine (((((hPA.and hDiv).and hGood).and hGeo).and hL3).and hFun).imp fun 𝒜 σ hsel H => ?_
  obtain ⟨⟨⟨⟨⟨hpa, hdv⟩, hgd⟩, hall⟩, hl3⟩, hfun⟩ := H
  choose τ hτ using fun {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) x hx i => hall Fm hc x hx i
  let τ' : _root_.GlobalTheory.Fc.CompatibleSelection σ := fun Fm hc x hx i => τ Fm hc x hx i
  have hduty : ∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm := fun _ Fm hc =>
    let ⟨_, _, h7, _⟩ := hsel Fm hc
    (DQ.familyClass_sevenDuties_and_stableLattices _ Fm h7).1
  have hiota : AtAll _root_.GlobalTheory.Fc.Ind.IotaPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := fun Fm hc x hx i => (hτ Fm hc x hx i).1
  have hppa : AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := fun Fm hc x hx i => hpa Fm hc x hx i
  have hpdiv : AtAll _root_.GlobalTheory.Fc.Ind.DivisorPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := fun Fm hc x hx i => _root_.GlobalTheory.Fc.StageZeroRow.p_div_at_piece_of_div3g _ (hdv Fm hc x hx i)
  have hcs : AtAll (fun D O c (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) => GlobalTheory.ExportPin.ClassSumPin b.pt ∧ b.pt.CompatibilityConditions) 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') :=
    fun Fm hc x hx i => ⟨(hτ Fm hc x hx i).2.1, (hτ Fm hc x hx i).2.2.1⟩
  have hrows : Ind.EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := _root_.GlobalTheory.T.eventually_pDiv_ties_of_class_sum_pin hDS hHC hCR hCW 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') hppa hpdiv hgd hcs
  have hmore : Ind.EvW (fun _ _ _ b => GlobalTheory.BigOn.More b.pt) 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') :=
    evW_of_atAll' fun Fm hc x hx i => (hτ Fm hc x hx i).2.2.2
  refine ⟨τ', ?_, hl3, _root_.GlobalTheory.T.eventually_norm_bound_of_more_points hOnto 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') hduty hrows hmore, _root_.GlobalTheory.T.eventually_L6_bound_of_lamLow hLam 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') hduty hrows, hfun⟩
  exact _root_.GlobalTheory.T.eventually_small_of_seeEx_primitive 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') (fun Fm hc x hx i =>
      _root_.GlobalTheory.T.indefinite_scale_theta_nonvanishing_alt hDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_root_.GlobalTheory.Fc.summandSelection σ τ' Fm hc x hx i).B.Q (_root_.GlobalTheory.Fc.summandSelection σ τ' Fm hc x hx i).pins
        (hiota Fm hc x hx i)) hppa
end GlobalTheory.Fc.StageZeroRow
end
