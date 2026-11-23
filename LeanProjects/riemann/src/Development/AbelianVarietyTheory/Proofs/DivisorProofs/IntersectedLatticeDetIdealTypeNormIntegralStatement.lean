import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectedLatticeDetIdealTypeNormIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie IsDedekindDomain
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectedLattice_detIdeal_typeNorm_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.LevOK N M → ℓ.Prime → ∀ (A : GlobalTheory.PlaceInt.Adapt Λ N ℓ) (s : c.F), Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ → ∀ (T : CDVR) (io : c.F →+* T.Fr), ¬ IsUnit (ℓ : T.V) → ∀ e : ℕ, 0 ≤ nval T.V e (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) := by
  first | exact @GlobalTheory.LatticeIndex.intersected_integral | exact GlobalTheory.LatticeIndex.intersected_integral | (intros; apply GlobalTheory.LatticeIndex.intersected_integral <;> assumption)
