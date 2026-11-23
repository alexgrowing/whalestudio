import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartitionSelectionEvaluation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualRowsOfClassSumsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualOntoOfMorePointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualL6OfLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualSmallOfPartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaNonvanishingStatement
import Formalism.LocalToGlobal.Divisibility.TupUsed
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.StageZeroRow

theorem tupAllUsed_at_part {D : D7} {O : Obj D} {c : ℝ} (b : Ind.Part D O c) : Formalism.L2.DIV.TupAllUsed b.P := by
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

theorem pDiv_at_part {D : D7} {O : Obj D} {c : ℝ} (b : Ind.Part D O c) (h : GlobalTheory.Cp.DivRows3G b.P) : Ind.PDiv D O c b :=
  Formalism.L2.DIV.DivRows3G.toRows (tupAllUsed_at_part b)
    ⟨h.sharpRR, h.baseRR, h.divisionRows_rationalLift, h.thTheta, ⟨h.num.Ij, h.num.jw, h.num.etaJ⟩, h.colsBk⟩

theorem evW_of_atAll' {Bd : BdT} {q : BdP Bd} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} (h : AtAll q 𝒜 σ) : Ind.EvW q 𝒜 σ :=
  Closed.of_all fun Fm _ hc => Ind.ev_of_atAll h Fm (w3_a hc)

theorem row_rRows_stage0 : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.BigOn.OntoX → GlobalTheory.BigTop.LamLow → ∀ (Q : V4.Slot) (Lk : LkT Bundle), R1.PeriodAdmissibilityAtBundlePoints Q Lk → R1.DivisorConditionAtBundlePoints Q Lk → RL.GoodReductionCondition Q Lk → S0.GeometricWeakCompatibility Q Lk → S0.CovolumeBound' Q Lk → S0.FunctorialityCondition Q Lk → RL.MultiplicityCondition' Q Lk → RL.KappaCondition Q Lk → RL.DifferentialCondition Q Lk → R1.RestRowsConditionAtBundlePoints DRS Q Lk := by
  intro hDS hHC hCR hCW hDC hOnto hLam Q Lk hPA hDiv hGood hGeo hL3 hFun hMi hKap hDf
  refine GlobalTheory.Fc.row_rRows_of_parts DRS Q Lk ?_ hMi hKap hDf
  refine (((((hPA.and hDiv).and hGood).and hGeo).and hL3).and hFun).imp fun 𝒜 σ hsel H => ?_
  obtain ⟨⟨⟨⟨⟨hpa, hdv⟩, hgd⟩, hall⟩, hl3⟩, hfun⟩ := H
  choose τ hτ using fun {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) x hx i => hall Fm hc x hx i
  let τ' : TieSel σ := fun Fm hc x hx i => τ Fm hc x hx i
  have hduty : ∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm := fun _ Fm hc =>
    let ⟨_, _, h7, _⟩ := hsel Fm hc
    (DQ.familyClass_sevenDuties_and_stableLattices _ Fm h7).1
  have hiota : AtAll Ind.PIota 𝒜 (partSel σ τ') := fun Fm hc x hx i => (hτ Fm hc x hx i).1
  have hppa : AtAll Ind.PPA 𝒜 (partSel σ τ') := fun Fm hc x hx i => hpa Fm hc x hx i
  have hpdiv : AtAll Ind.PDiv 𝒜 (partSel σ τ') := fun Fm hc x hx i => pDiv_at_part _ (hdv Fm hc x hx i)
  have hcs : AtAll (fun D O c (b : Ind.Part D O c) => GlobalTheory.ExportPin.ClassSumPin b.pt ∧ b.pt.Ties) 𝒜 (partSel σ τ') :=
    fun Fm hc x hx i => ⟨(hτ Fm hc x hx i).2.1, (hτ Fm hc x hx i).2.2.1⟩
  have hrows : Ind.EvW Ind.PRows 𝒜 (partSel σ τ') := GlobalTheory.T.eventual_rows_of_class_sums hDS hHC hCR hCW 𝒜 (partSel σ τ') hppa hpdiv hgd hcs
  have hmore : Ind.EvW (fun _ _ _ b => GlobalTheory.BigOn.More b.pt) 𝒜 (partSel σ τ') :=
    evW_of_atAll' fun Fm hc x hx i => (hτ Fm hc x hx i).2.2.2
  refine ⟨τ', ?_, hl3, GlobalTheory.T.eventual_onto_of_more_points hOnto 𝒜 (partSel σ τ') hduty hrows hmore, GlobalTheory.T.eventual_L6_of_lower_bound hLam 𝒜 (partSel σ τ') hduty hrows, hfun⟩
  exact GlobalTheory.T.eventual_small_of_parts 𝒜 (partSel σ τ') (fun Fm hc x hx i =>
      GlobalTheory.T.indefinite_scale_theta_nonvanishing hDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (partSel σ τ' Fm hc x hx i).B.Q (partSel σ τ' Fm hc x hx i).pins
        (hiota Fm hc x hx i)) hppa

end GlobalTheory.Fc.StageZeroRow
