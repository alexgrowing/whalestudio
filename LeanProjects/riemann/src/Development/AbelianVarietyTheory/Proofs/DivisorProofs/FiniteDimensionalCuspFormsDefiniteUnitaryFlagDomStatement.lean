import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspFormsDefiniteUnitaryFlagDom
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_cuspForms_definiteUnitaryFlagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (X.p0 = 0 ∨ X.p0 = r) → ∀ la : Wt X.Ψ r, FiniteDimensional ℂ (Submodule.span ℂ ((fun f : Frame X.Ψ r → ℂ => fun x : X.dom => f x) '' X.SS la)) := by
  first | exact @GlobalTheory.DefiniteFin.finiteDimensional_cusp_definite | exact GlobalTheory.DefiniteFin.finiteDimensional_cusp_definite | (intros; apply GlobalTheory.DefiniteFin.finiteDimensional_cusp_definite <;> assumption)
