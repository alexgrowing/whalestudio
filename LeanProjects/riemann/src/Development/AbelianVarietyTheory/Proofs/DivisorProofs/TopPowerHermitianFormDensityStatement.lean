import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPowerHermitianFormDensity
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open GlobalTheory.CxForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_power_hermitian_form_density : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), GlobalTheory.CxForm.dens (((∑ a, ∑ b, H a b • GlobalTheory.CxForm.sym (a, b) : GlobalTheory.CxForm.Ev n) ^ n : GlobalTheory.CxForm.Ev n) : GlobalTheory.CxForm.Alt n) = (n.factorial : ℂ) * H.det / (Complex.I / 2) ^ n := by
  first | exact @GlobalTheory.CxForm.DensPow.dens_pow | exact GlobalTheory.CxForm.DensPow.dens_pow | (intros; apply GlobalTheory.CxForm.DensPow.dens_pow <;> assumption)
