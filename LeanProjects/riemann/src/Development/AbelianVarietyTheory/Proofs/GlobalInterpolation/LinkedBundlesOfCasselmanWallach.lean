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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeServiceGlobalReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowAAtGAtBuilt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DivisionSecondComplementConstructedPoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowJOnOfRowHPA
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodEntriesAtBuiltStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassCountBoundParamsLambdaConstructedPoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowHInstROfHU
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LPrjSurjAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TupAllUsedAtPart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHyperplaneVolumeRatioSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtChoice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowCountsOfLabels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowHTwOfTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowRepresentationBasePosition
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.AllAtMemberStage0

section large₂

variable {KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop} {Q Q' : V4.Slot}

theorem eventually_coreProperty_of_forall {r : V4.Slot → Prop} (h : ∀ S, r S) : Lg1 KP Q Q' r :=
  ⟨fun _ _ _ _ _ => True, largeBaseProperty_true, h _⟩

theorem eventually_coreProperty_mono {r r' : V4.Slot → Prop} (h : Lg1 KP Q Q' r) (hi : ∀ S, r S → r' S) : Lg1 KP Q Q' r' :=
  let ⟨R, hR, h⟩ := h; ⟨R, hR, hi _ h⟩

theorem forall_linked_bundles_and {Lk : LkT Bundle} {H H' : ∀ 𝒜 : FamClass, RawSel Bundle 𝒜 → Prop}
    (h : Lg1 KP Q Q' fun S => Row S Lk H) (h' : Lg1 KP Q Q' fun S => Row S Lk H') :
    Lg1 KP Q Q' fun S => Row S Lk fun 𝒜 σ => H 𝒜 σ ∧ H' 𝒜 σ :=
  RowL.and (KP := KP) (Q := Q) (Q' := Q') h h'

end large₂

theorem linkR_of_isLinked {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) (K : Ctx) (β : BPt K) (c : ℝ) (b : Bundle β.D β.O c)
    (h : IsLinked p K β c b) : LinkR p K β c b.R := by
  obtain ⟨q, b', ⟨w⟩, e⟩ := h
  refine ⟨q, b'.R, w.recPin, ?_⟩
  exact congrArg (fun t : Σ (D : D7) (O : Obj D), Bundle D O c => (⟨t.1, t.2.1, t.2.2.R⟩ : Σ (D : D7) (O : Obj D), BdRec D O c)) e

theorem allRows_of_open0 : GlobalTheory.Published.GlobalArtinReciprocity → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.BigOn.OntoX → GlobalTheory.BigTop.LamLow → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP) (NN : FamClass → Prop), S0.Open0 (prmR N S Γ) → RL.At (prmR N S Γ) S0.CovolumeBound' → RL.At (prmR N S Γ) S0.FunctorialityCondition → RL.At (prmR N S Γ) (fun Q L => R1.PredicateAtBundlePoints Q L NN) → AllRows KPx (IsBuiltE (prmR N S Γ).s) (IsGoodE (prmR N S Γ).s) (IsLinked (prmR N S Γ)) NN DRS := by
  intro hA hSW p1 p2 p3 p4 p5 h3 h4 hL N S Γ NN o hl3 hfun hN
  have six := GlobalTheory.T.period_entries_at_built (prmR N S Γ).s (IsLinked (prmR N S Γ))
  have hU := GlobalTheory.VolRatioFromSiegelWeil.volumeRatio hSW
  have loc := GlobalTheory.LocalRows.rows_lg hSW KPx (IsBuiltE (prmR N S Γ).s) (IsGoodE (prmR N S Γ).s) (IsLinked (prmR N S Γ))
  exact
    { hn4 := eventually_coreProperty_of_forall fun Q => (R0.classCountBound_paramsLambda_constructedPoints _ Q _).1
      jOn := eventually_coreProperty_mono o.hPA fun Q h => JOnBundle.row_jOn_of_row_hPA Q _ h
      hInstR := eventually_coreProperty_of_forall fun Q => GlobalTheory.row_hInstR_of_hU hU _ Q _
      aC2 := eventually_coreProperty_of_forall fun Q => ClassTwoEntries.divisionSecondComplement_constructedPoints _ Q _
      aP10 := six.2.2.2.2.2
      aAtG := row_aAtG_at_built _ rfl _
      aPt0 := six.1
      aPtTw := six.2.1
      aPer0 := six.2.2.1
      aPerTw := six.2.2.2.1
      tie := six.2.2.2.2.1
      hRB := eventually_coreProperty_of_forall fun Q => R1.row_hRB_univ p1 p2 p3 p4 Q _
      hTw := eventually_coreProperty_mono o.tie fun Q h => row_hTw_of_tie Q _ h
      hPA := o.hPA
      hLamP := o.hLamP
      hDivG := o.hDivG
      hDcPtG := o.hDcPtG
      selJ := o.selJ
      sLp := loc.1
      sO := loc.2.1
      hServ := RL.At.of_row (GlobalTheory.T.hecke_service_global_reciprocity hA (prmR N S Γ) _ (linkR_of_isLinked _))
      zL := eventually_coreProperty_mono o.hPA fun Q h => R1.ZLAt.row_zL Q _ h
      hTF := loc.2.2
      c30 := GlobalTheory.CountRowByName.row_counts_of_labels hSW KPx _ _ _ o.lab
      rRows := eventually_coreProperty_mono (forall_linked_bundles_and (forall_linked_bundles_and (forall_linked_bundles_and o.hPA o.hDivG) (forall_linked_bundles_and o.good o.geo))
          (forall_linked_bundles_and (forall_linked_bundles_and hl3 hfun) (forall_linked_bundles_and (forall_linked_bundles_and o.mi o.kap) o.df)))
        fun Q h => StageZeroRow.row_rRows_stage0 p1 p2 p3 p4 p5 h3 h4 Q _
          (h.imp fun _ _ _ t => t.1.1.1) (h.imp fun _ _ _ t => t.1.1.2) (h.imp fun _ _ _ t => t.1.2.1)
          (h.imp fun _ _ _ t => t.1.2.2) (h.imp fun _ _ _ t => t.2.1.1) (h.imp fun _ _ _ t => t.2.1.2)
          (h.imp fun _ _ _ t => t.2.2.1.1) (h.imp fun _ _ _ t => t.2.2.1.2) (h.imp fun _ _ _ t => t.2.2.2)
      nRest := hN }

end GlobalTheory.Fc.AllAtMemberStage0
