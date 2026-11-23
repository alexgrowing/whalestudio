import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltIntegersCpEquivCompatibleUntilt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import GroundTheory.PAdicHodge.TiltValuation
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tiltIntegersCpEquiv_compatible_untilt : ∀ (l : ℕ) [Fact l.Prime], ∃ e : Fl l ≃+* PreTilt (GroundTheory.PAdicHodge.normInteger ℂ_[l]) l, ∀ x : Fl l, ((PreTilt.untilt (e x) : GroundTheory.PAdicHodge.normInteger ℂ_[l]) : ℂ_[l]) = sh x := by
  first | exact @GlobalTheory.PSer.exists_flEquiv_untilt | exact GlobalTheory.PSer.exists_flEquiv_untilt | (intros; apply GlobalTheory.PSer.exists_flEquiv_untilt <;> assumption)
