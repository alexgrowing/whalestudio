import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlobalSectionsDimNefPowTensorAmpleIsBi
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbH0_nef_pow_tens_ample_le_mul_pow_dim : GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] (Z : Scheme.{0}) [Algebra F Γ(Z, ⊤)] (d : ℕ), IsProjOver (strHom F Z) → topologicalKrullDim Z ≤ d → ∀ L A : LB Z, IsNef F L → IsAmpleLB A → ∃ C : ℝ, ∀ᶠ m : ℕ in atTop, (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ C * (m : ℝ) ^ d := by
  first | exact @GlobalTheory.NefGrowth.lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO | exact GlobalTheory.NefGrowth.lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO | (intros; apply GlobalTheory.NefGrowth.lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO <;> assumption)
