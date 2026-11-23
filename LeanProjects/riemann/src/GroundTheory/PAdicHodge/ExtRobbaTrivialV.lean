import Mathlib
import GroundTheory.PAdicHodge.SlopeFiltration
import GroundTheory.PAdicHodge.ExtRobbaEigen
import GroundTheory.PAdicHodge.ExtRobbaOrd
import GroundTheory.PAdicHodge.DMTeichPow
import GroundTheory.PAdicHodge.DMTeichBasic
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable (F : T.TeichFrob) [CompleteSpace L]

def πEdag (T : TeichLift p L Γ) : T.Edag :=
  ⟨algebraMap Γ T.B T.π, T.Econ_le_Edag ⟨1 / 2, by norm_num, by norm_num⟩
    (T.algebraMap_π_mem_Econ _)⟩

theorem edagToTilde_πEdag : T.edagToTilde (πEdag T) = T.πTilde := rfl

theorem ordB_algebraMap_π_pow_mul (m : ℕ) {c : T.B} (hc : c ≠ 0) :
    T.ordB (algebraMap Γ T.B T.π ^ m * c) = m + T.ordB c := by
  have h1 : algebraMap Γ T.B T.π ^ m = ((T.piB ^ (m : ℤ) : T.Bˣ) : T.B) * algebraMap Γ T.B 1 := by
    rw [map_one, mul_one, zpow_natCast, Units.val_pow_eq_pow_val, piB_val]
  have h1' : T.ordB (algebraMap Γ T.B T.π ^ m) = m := by
    rw [h1]; exact T.ordB_piB_zpow_mul _ (by rw [map_one]; exact one_ne_zero)
  have hne : algebraMap Γ T.B T.π ^ m ≠ 0 := by
    have := T.nontrivial_B
    exact ((IsLocalization.Away.algebraMap_isUnit T.π).pow m).ne_zero
  rw [T.ordB_mul hne hc, h1']

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
