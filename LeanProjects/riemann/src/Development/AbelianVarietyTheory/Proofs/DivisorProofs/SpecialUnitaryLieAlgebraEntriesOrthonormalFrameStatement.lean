import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryLieAlgebraEntriesOrthonormalFrame
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialUnitaryLieAlgebra_entries_orthonormal_frame : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∀ (Y : EuclideanSpace ℂ (X.Ψ × Fin r × Fin r)), fromFrame x Y ∈ realLie X.Ψ X.Gm → (∀ τ a b, Y (τ, b, a) = -((sgn X.p0 a * sgn X.p0 b : ℝ) : ℂ) * conj (Y (τ, a, b))) ∧ ∀ τ, ∑ a, Y (τ, a, a) = 0 := by
  first | exact @GlobalTheory.SUVol.FrameSkew.entries_of_mem | exact GlobalTheory.SUVol.FrameSkew.entries_of_mem | (intros; apply GlobalTheory.SUVol.FrameSkew.entries_of_mem <;> assumption)
