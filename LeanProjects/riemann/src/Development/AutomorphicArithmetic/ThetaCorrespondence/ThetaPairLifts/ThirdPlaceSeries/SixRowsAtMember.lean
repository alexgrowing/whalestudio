import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodEntriesAtBuilt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc
theorem six_rows_at_member_alt : ∀ (𝒮 : Slots) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition),
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.ReferenceChainEvaluationAtBundlePoints S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.TwistedPointAtBundlePoints S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.PeriodAtZeroAtBundlePoints S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.TwistedPeriodAtBundlePoints S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.Row_tie S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => AllBundlePointProperties.LevelPrimeColumnValuationsAtBundlePoints S Lk) := by
  intro 𝒮 Lk
  have hC : OverCols (sAnd (IsGoodE 𝒮) fun _ _ _ _ _ => True) :=
    (GlobalTheory.T.goodTwistCores_over_trueColumns 𝒮 (fun _ _ _ _ _ => True)).2
  have hT : LargeBaseCondition KPx (IsBuiltE 𝒮) fun _ _ _ _ _ => True := largeBaseProperty_true
  exact ⟨⟨_, hT, GlobalTheory.T.referenceChainEvaluationAtBundlePoints_of_overCols _ hC _ Lk⟩, ⟨_, hT, GlobalTheory.T.twistedChainEvaluation_rational_integral_bundlePoints _ hC _ Lk⟩,
    ⟨_, hT, GlobalTheory.T.referencePeriodIntegral_bundlePoints_of_overColumns _ hC _ Lk⟩, ⟨_, hT, GlobalTheory.T.twistedPeriods_integral_at_bundlePoints _ hC _ Lk⟩,
    ⟨_, hT, GlobalTheory.T.realSideColumnsCompatible_bundlePoints_overColumns _ hC _ Lk⟩, ⟨_, hT, GlobalTheory.T.levelPrimeColumnValuations_bundlePoints_overColumns _ hC _ Lk⟩⟩
end GlobalTheory.Fc
end
