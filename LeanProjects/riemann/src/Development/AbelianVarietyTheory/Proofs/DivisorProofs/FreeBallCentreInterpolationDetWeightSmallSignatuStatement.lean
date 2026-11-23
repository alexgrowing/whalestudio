import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeBallCentreInterpolationDetWeightSmallSignatu
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeBallCentre_interpolation_detWeight_smallSignature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ la, ∀ γ ∈ X.Γ, X.χ la γ = 1) → ∀ (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r), IsOrth X x0 → GlobalTheory.Up.FreeBall X G x0 (1 / (49 * (r : ℝ) ^ 2)) → 0 < X.p0 → X.p0 < r → X.p0 * (r - X.p0) ≤ 3 → ∀ s : ℕ, Even s → 2 * r + 50 * r ^ 2 * (X.Ψ.card * (X.p0 * (r - X.p0))) + 1 ≤ s → ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x0 ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → P (lact γ x0) = 0 := by
  first | exact @GlobalTheory.Up.OrbitInterpSmall.orbit_interp_small | exact GlobalTheory.Up.OrbitInterpSmall.orbit_interp_small | (intros; apply GlobalTheory.Up.OrbitInterpSmall.orbit_interp_small <;> assumption)
