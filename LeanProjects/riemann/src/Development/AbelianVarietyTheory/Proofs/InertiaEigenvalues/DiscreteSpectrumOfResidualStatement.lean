import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_spectrum_of_residual : GlobalTheory.Published.DiscreteSpectrumResidual → GlobalTheory.Published.DiscreteSpectrumGL := by
  first | exact @GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual | exact GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual | (intros; apply GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual <;> assumption)
