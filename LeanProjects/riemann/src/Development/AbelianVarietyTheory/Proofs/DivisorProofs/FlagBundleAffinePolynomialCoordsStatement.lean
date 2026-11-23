import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleAffinePolynomialCoords
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_affine_polynomial_coords : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → (∀ a, IsVB (E a) (r a)) → ∀ (U : B.Opens), IsAffineOpen U → ∀ (eU : ∀ a, Fin (r a) → Γ(E a, U)), (∀ a, IsFrame (eU a)) → ∃ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), IsAffineOpen W ∧ ∃ n : (Σ a, Low (r a)) → Γ(Y, W), Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n) ∧ ∀ a, GlobalTheory.FlagCell.Spans (fl a) W (GlobalTheory.FlagCell.pullCol π (eU a) hW (GlobalTheory.FlagCell.uniR fun s => n ⟨a, s⟩)) := by
  first | exact @GlobalTheory.CellScheme.cell_affine | exact GlobalTheory.CellScheme.cell_affine | (intros; apply GlobalTheory.CellScheme.cell_affine <;> assumption)
