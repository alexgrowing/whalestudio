import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeHermitianEllipsoid
import Mathlib
open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_hermitian_ellipsoid' : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (r : ℝ), Hm.PosDef → 0 < r → volume {w : Fin g → ℂ | (w ⬝ᵥ Hm.mulVec (star w)).re < r ^ 2} = ENNReal.ofReal (Real.pi ^ g * r ^ (2 * g) / (g.factorial * Hm.det.re)) := by
  first | exact @GlobalTheory.volume_hermitian_ellipsoid | exact GlobalTheory.volume_hermitian_ellipsoid | (intros; apply GlobalTheory.volume_hermitian_ellipsoid <;> assumption)
