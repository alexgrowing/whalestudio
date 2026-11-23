import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import GroundTheory.PAdicHodge.TiltValuation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltIntegersCpEquivCompatibleUntiltStatement

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem untilt_injective_zero_and_dvd_of_norm_sh_le :
    ∀ (l : ℕ) [Fact l.Prime], (∀ x : Fl l, sh x = 0 → x = 0) ∧
      ∀ x y : Fl l, ‖sh x‖ ≤ ‖sh y‖ → y ∣ x := by
  intro l _
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_tiltIntegersCpEquiv_compatible_untilt l
  refine ⟨fun x hx => ?_, fun x y hxy => ?_⟩
  · have h0 : e x = 0 := GroundTheory.PAdicHodge.untilt_eq_zero_iff.1 (by rw [he]; exact hx)
    exact e.injective (by rw [h0, map_zero])
  · have hd : e y ∣ e x := by
      rw [GroundTheory.PAdicHodge.preTilt_dvd_iff_norm_le, GroundTheory.PAdicHodge.preTilt_norm_def,
        GroundTheory.PAdicHodge.preTilt_norm_def, he, he]
      exact hxy
    obtain ⟨c, hc⟩ := hd
    exact ⟨e.symm c, e.injective (by rw [map_mul, e.apply_symm_apply, hc])⟩

end GlobalTheory.PSer
