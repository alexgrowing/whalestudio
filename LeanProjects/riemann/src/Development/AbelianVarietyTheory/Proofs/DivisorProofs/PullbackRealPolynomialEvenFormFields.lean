import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm

theorem algHom_aeval_ev {m m' : ℕ} {ι : Type} (φ : Alt m →ₐ[ℂ] Alt m') (u : ι → Ev m) (u' : ι → Ev m')
    (h : ∀ i, φ (u i : Alt m) = (u' i : Alt m')) (P : MvPolynomial ι ℝ) :
    φ ((aeval u (P.map (algebraMap ℝ ℂ)) : Ev m) : Alt m) = ((aeval u' (P.map (algebraMap ℝ ℂ)) : Ev m') : Alt m') := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.map_C, MvPolynomial.aeval_C]
    exact φ.commutes _
  | add p q hp hq =>
    simp only [map_add, Subalgebra.coe_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, Subalgebra.coe_mul, hp, h]

theorem pullback_evalF : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n') (g : M' → M) (ι : Type) (w : ι → A.Pt → Ev n) (w' : ι → A'.Pt → Ev n'), (∀ i, A.pullback A' g (fld A (w i)) = fld A' (w' i)) → ∀ P : MvPolynomial ι ℝ, A.pullback A' g (evalF A w P) = evalF A' w' P := by
  intro M M' _ _ n n' A A' g ι w w' hw P
  funext x
  exact algHom_aeval_ev _ _ _ (fun i => congrFun (hw i) x) P

end GlobalTheory.LineForm
