import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsChartIndependence
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vectors_chart_independence : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X0 : Scheme.{0}} (t : ReciprocityTheory.ChartRestriction.G.Geo.Tor.SAB H X0) {K : Type} [Field K] (ι : K →+* Qb) (x0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ X0) {m : ℕ} (uK : Fin m → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ t.G.left)), (∀ j, Formalism.L2.Pj.IsTanAtG t (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ι ≫ x0) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ι) ≫ uK j)) → (∀ w, Formalism.L2.Pj.IsTanAtG t (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ι ≫ x0) w → ∃! a : Fin m → Qb, Formalism.L2.Pj.IsCombAtG t (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ι ≫ x0) (fun j => ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ι) ≫ uK j) a w) → (∀ j, Formalism.L2.Pj.IsTanAtG t x0 (uK j)) ∧ ∀ w, Formalism.L2.Pj.IsTanAtG t x0 w → ∃! c : Fin m → K, Formalism.L2.Pj.IsCombAtG t x0 uK c w := by
  first | exact @GlobalTheory.TanDescent.basis_descent | exact GlobalTheory.TanDescent.basis_descent | (intros; apply GlobalTheory.TanDescent.basis_descent <;> assumption)
