import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernDens_detWeight_eq_neg_levi_log : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), (∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → IsDens fun (c : AlgChart p σ 1) y => c.chernDens φ y) ∧ ∀ (L : X.Modules) (g : Met p σ L 1), g.IsCInf → ∀ (U : X.Opens) (t : Γ(L, U)), IsFrame (fun _ : Fin 1 => t) → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∈ ptsIn p σ U → c.chernDens g.detWeight y = -(leviForm (fun v => Real.log (g.form t t (c.e.symm v)).re) (c.e y) (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)).re / Real.pi := by
  first | exact @GlobalTheory.CurveDens.chernDens_curve | exact GlobalTheory.CurveDens.chernDens_curve | (intros; apply GlobalTheory.CurveDens.chernDens_curve <;> assumption)
