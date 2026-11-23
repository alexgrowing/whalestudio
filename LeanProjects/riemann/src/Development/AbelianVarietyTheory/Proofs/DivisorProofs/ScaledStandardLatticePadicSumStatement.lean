import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledStandardLatticePadicSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt GlobalTheory.LieRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_standard_lattice_padic_sum : ∀ (K : Type) [Field K] [NumberField K] (g p : ℕ) [Fact p.Prime] (D : ℕ), 0 < D → ∑ᶠ j : K →+* ℂ_[p], ∑ k : Fin g, lnGrP p j (Submodule.span (𝓞 K) (Set.range fun i : Fin g => (D : K) • (Pi.single i 1 : Fin g → K))) k = g * Module.finrank ℚ K * ((padicValNat p D : ℝ) * Real.log p) := by
  first | exact @GlobalTheory.StdScaleLat.sum_lnGrP_scaled | exact GlobalTheory.StdScaleLat.sum_lnGrP_scaled | (intros; apply GlobalTheory.StdScaleLat.sum_lnGrP_scaled <;> assumption)
