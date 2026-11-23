import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomTiltMapTiltFrobeniusIntegerPower
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_tilt_map_tiltFrobeniusIntegerPower : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] [CharP F l] [PerfectRing F l]
    (ι : Fl l →+* F) (k : ℤ) (x : Fl l), ι (GlobalTheory.PSer.pw k x) = GlobalTheory.PMonE.pw l k (ι x) := by
  first | exact @GlobalTheory.PSer.map_pw_eq_pw | exact GlobalTheory.PSer.map_pw_eq_pw | (intros; apply GlobalTheory.PSer.map_pw_eq_pw <;> assumption)
