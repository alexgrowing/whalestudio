import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionLimit
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
theorem _root_.GlobalTheory.T.arithmetic_function_limit : ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ t : ℝ → ℝ, Tendsto t atTop (𝓝 0) → ∀ (ι : Type) [Fintype ι] (L : ℝ → ι → HermLB p) (L₀ : ι → HermLB p), (∀ i, LFam t (fun R => L R i) (L₀ i)) → ∀ (Φ : ℝ → MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (Φ₀ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), (∀ R, IsArFun (L R) D (Φ R)) → IsArFun L₀ D Φ₀ → ∀ P, Tendsto (fun R => Φ R P) atTop (𝓝 (Φ₀ P)) := by
  first | exact @GlobalTheory.MetFam.MixedCont.tendsto_isArFun | exact GlobalTheory.MetFam.MixedCont.tendsto_isArFun | (intros; apply GlobalTheory.MetFam.MixedCont.tendsto_isArFun <;> assumption)
