import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharDeterminantIdealUnitarySmulSelfDual
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.char_determinantIdeal_unitary_smul_selfDual : ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ {N : ℕ} (M : SDLat D.host.E N) (e : Matrix (Fin N) (Fin N) D.host.E), e * star e = 1 → χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (SDLat.smulLat e M.1)) = (∏ τ, TaylorLogMetric.embT D τ e.det)⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) M.1) := by
  first | exact @GlobalTheory.ChiMove.chi_detId_smulLat | exact GlobalTheory.ChiMove.chi_detId_smulLat | (intros; apply GlobalTheory.ChiMove.chi_detId_smulLat <;> assumption)
