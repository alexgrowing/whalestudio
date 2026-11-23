import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ChoiceFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniq

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf

theorem isLowUnitH_base_vector {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) :
    IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ) := by
  obtain ⟨P, hP, hmem⟩ := C.y_low τ
  refine ⟨P, hP, ?_, hmem⟩
  obtain ⟨-, hiso⟩ := Formalism.L2.SG.Pf.WuBL.sigB_rep C τ
  show ‖X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ))‖ = 1
  rw [← (X.low (vOf X τ)).1]
  exact hiso (C.y τ) (C.y_mem τ) (X.B.w (vOf X τ))

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem goodSRest_all {D : D7} {X : HidaSetting D} {θ : ℝ} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (hT : Formalism.BasicNotions.dsigTie D) {C : Choice X θ} (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    GoodSRest hB u u' τ :=
  goodSRest_of_loc (Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) hB u u' τ
    (Formalism.L2.SG.Pf.WuDec.lowSmoothSK (dsTr C τ) (isLowUnitH_base_vector C τ)) hT

end Formalism.L2.SG.Pf
