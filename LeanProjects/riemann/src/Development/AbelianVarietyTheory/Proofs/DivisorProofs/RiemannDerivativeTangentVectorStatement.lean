import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannDerivativeTangentVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_derivative_tangent_vector : ∀ (T : Scheme.{0}) (P : PPAS T) (y₀ : Sp ℂ ⟶ T) (d : P.RiemannData y₀) (X : Scheme.{0}) (θ : P.A.left ⟶ X) (W : X.Opens), ⊤ ≤ (y₀ ≫ LieVB.unitSec P.A) ⁻¹ᵁ (θ ⁻¹ᵁ W) → ∀ (f : Γ(X, W)) (v : epsR ℂ ⟶ d.B) (w : Fin P.g → ℂ), IsTangent v → d.u.IsDiff w v → TrivSqZeroExt.snd (valR (v.left ≫ d.φ ≫ θ) W f) = ∑ a, w a * d.cov (θ ⁻¹ᵁ W) (θ.appLE W (θ ⁻¹ᵁ W) le_rfl f) a := by
  first | exact @GlobalTheory.PPAS.RiemannData.snd_valR_tangent | exact GlobalTheory.PPAS.RiemannData.snd_valR_tangent | (intros; apply GlobalTheory.PPAS.RiemannData.snd_valR_tangent <;> assumption)
