import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DdcCompositionLeviForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_composition_levi_form : ∀ (ι : Type) [Fintype ι] (p q d : ℕ) (F : Pt ι p q → ReciprocityTheory.L2DbarEstimates.V d) (u : ReciprocityTheory.L2DbarEstimates.V d → ℝ) (z : Pt ι p q), (∀ᶠ v in nhds (flat z), DifferentiableAt ℂ (fun w => F (unflat w)) v) → ContDiffAt ℝ 2 u (F z) → ∀ ξ, ddc (u ∘ F) z ξ = (ReciprocityTheory.L2DbarEstimates.leviV d (fun v => (u v : ℂ)) (F z) (fderiv ℂ (fun w => F (unflat w)) (flat z) (flat ξ)).ofLp).re / Real.pi := by
  first | exact @GlobalTheory.HodgeDomain.ddc_comp_holo | exact GlobalTheory.HodgeDomain.ddc_comp_holo | (intros; apply GlobalTheory.HodgeDomain.ddc_comp_holo <;> assumption)
