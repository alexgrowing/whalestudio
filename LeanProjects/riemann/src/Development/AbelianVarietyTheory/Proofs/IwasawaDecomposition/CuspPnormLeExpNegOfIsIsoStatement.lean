import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspPnormLeExpNegOfIsIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pnorm_le_exp_neg_of_mem_SS_of_isIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (la : Wt X.Ψ N) (P : Frame X.Ψ N → ℂ) (ξ : Fin N → E), P ∈ X.SS la → X.IsIso ξ → ∃ C c : ℝ, 0 < c ∧ ∀ x ∈ X.dom, ∀ t : ℝ, 1 ≤ t → (∀ τ, t ≤ X.tt ξ x τ) → X.pnorm la P x ≤ C * Real.exp (-c * t) := by
  first | exact @GlobalTheory.cusp_pnorm_le_exp_neg_of_isIso | exact GlobalTheory.cusp_pnorm_le_exp_neg_of_isIso | (intros; apply GlobalTheory.cusp_pnorm_le_exp_neg_of_isIso <;> assumption)
