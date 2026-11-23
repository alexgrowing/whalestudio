import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BothRowsFromSiegelWeil
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LoopRowsOfRowsFinDim
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.Cp
namespace GlobalTheory.LocalRows
theorem at_choice_alt (hSW : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent) (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) :
    _root_.GlobalTheory.Fc.R1.SelectionLpBound 𝒜 σ ∧ _root_.GlobalTheory.Fc.R1.SelectionOrderBound 𝒜 σ ∧ R1.H_hTF 𝒜 := by
  let T : _root_.Formalism.L2.TwistSelection (D3 3 𝒜) := fun Fm hc => (_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc)
  have hB := _root_.GlobalTheory.bothRowsFromSiegelWeil_alt hSW (D3 3 𝒜) T
  have hL : _root_.GlobalTheory.Fc.R1.SelectionLpBound 𝒜 σ :=
    _root_.GlobalTheory.LoopRowsByName.loopRows_of_rowsFinDim_alt GlobalTheory.rowsFinDim_link (GlobalTheory.VolRatioFromSiegelWeil.volumeRatio hSW) (D3 3 𝒜) T _ (fun Fm hw => hw.2.2.1)
  exact ⟨hL, GlobalTheory.CarrierGap.offDiag (GlobalTheory.St.swxs_of_siegelWeil hSW) (GlobalTheory.rowNGP_of_siegelWeil hSW) GlobalTheory.rowsFinDim_link (D3 3 𝒜) _
    (fun Fm hc x hx h i => ((_root_.GlobalTheory.Fc.spectralConditionOfRawSelection σ) Fm (d3_a hc) x hx h i).locTied) hB.1 hL, hB.2⟩
theorem sLp_sO_hTF_of_siegelWeil : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), _root_.GlobalTheory.Fc.R1.SlotLpCondition Q Lk ∧ _root_.GlobalTheory.Fc.R1.SlotOrderCondition Q Lk ∧ _root_.GlobalTheory.Fc.R1.SlotTorsionFreeCondition Q Lk := fun hSW Q Lk =>
  ⟨Row.of_sel fun 𝒜 σ _ => (_root_.GlobalTheory.LocalRows.at_choice_alt hSW 𝒜 σ).1, Row.of_sel fun 𝒜 σ _ => (_root_.GlobalTheory.LocalRows.at_choice_alt hSW 𝒜 σ).2.1,
    Row.of_sel fun 𝒜 σ _ => (_root_.GlobalTheory.LocalRows.at_choice_alt hSW 𝒜 σ).2.2⟩
theorem lg1_sLp_sO_hTF : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), (Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotLpCondition S Lk) ∧ (Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotOrderCondition S Lk) ∧ Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotTorsionFreeCondition S Lk := fun hSW KP Q Q' Lk =>
  ⟨⟨_, largeBaseProperty_true, (_root_.GlobalTheory.LocalRows.sLp_sO_hTF_of_siegelWeil hSW _ Lk).1⟩, ⟨_, largeBaseProperty_true, (_root_.GlobalTheory.LocalRows.sLp_sO_hTF_of_siegelWeil hSW _ Lk).2.1⟩, ⟨_, largeBaseProperty_true, (_root_.GlobalTheory.LocalRows.sLp_sO_hTF_of_siegelWeil hSW _ Lk).2.2⟩⟩
end GlobalTheory.LocalRows
end
