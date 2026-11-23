import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoopRowOfFiniteDim
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OffK0Closed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RanksFramesOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsFinDimLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowPositivityOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHyperplaneVolumeRatioSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SwxsOfSiegelWeil
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.Cp

namespace GlobalTheory.LocalRows

theorem at_choice (hSW : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent) (𝒜 : FamClass) (σ : RawSel Bundle 𝒜) :
    R1.H_sLp 𝒜 σ ∧ R1.H_sO 𝒜 σ ∧ R1.H_hTF 𝒜 := by
  let T : Formalism.L2.TSel (D3 3 𝒜) := fun Fm hc => (sel σ) Fm (d3_a hc)
  have hB := GlobalTheory.bothRowsFromSiegelWeil hSW (D3 3 𝒜) T
  have hL : R1.H_sLp 𝒜 σ :=
    GlobalTheory.LoopRowsByName.loopRows_of_rowsFinDim GlobalTheory.rowsFinDim_link (GlobalTheory.VolRatioFromSiegelWeil.volumeRatio hSW) (D3 3 𝒜) T _ (fun Fm hw => hw.2.2.1)
  exact ⟨hL, GlobalTheory.CarrierGap.offDiag (GlobalTheory.St.swxs_of_siegelWeil hSW) (GlobalTheory.rowNGP_of_siegelWeil hSW) GlobalTheory.rowsFinDim_link (D3 3 𝒜) _
    (fun Fm hc x hx h i => ((selS σ) Fm (d3_a hc) x hx h i).locTied) hB.1 hL, hB.2⟩

theorem what₂ : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (Q : V4.Slot) (Lk : LkT Bundle), R1.LpSelectionAtBundlePoints Q Lk ∧ R1.IntegralSelectionAtBundlePoints Q Lk ∧ R1.TorsionFreenessAtBundlePoints Q Lk := fun hSW Q Lk =>
  ⟨Row.of_sel fun 𝒜 σ _ => (at_choice hSW 𝒜 σ).1, Row.of_sel fun 𝒜 σ _ => (at_choice hSW 𝒜 σ).2.1,
    Row.of_sel fun 𝒜 σ _ => (at_choice hSW 𝒜 σ).2.2⟩

theorem rows_lg : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT Bundle), (Lg1 KP Q Q' fun S => R1.LpSelectionAtBundlePoints S Lk) ∧ (Lg1 KP Q Q' fun S => R1.IntegralSelectionAtBundlePoints S Lk) ∧ Lg1 KP Q Q' fun S => R1.TorsionFreenessAtBundlePoints S Lk := fun hSW KP Q Q' Lk =>
  ⟨⟨_, largeBaseProperty_true, (what₂ hSW _ Lk).1⟩, ⟨_, largeBaseProperty_true, (what₂ hSW _ Lk).2.1⟩, ⟨_, largeBaseProperty_true, (what₂ hSW _ Lk).2.2⟩⟩

end GlobalTheory.LocalRows
