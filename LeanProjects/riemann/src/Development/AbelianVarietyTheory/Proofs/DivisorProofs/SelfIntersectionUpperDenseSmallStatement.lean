import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionUpperDenseSmall
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolHomog
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_intersection_upper_dense_small : GlobalTheory.Published.VolGe → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (a e : ℝ), L.SemiPos D → NefFib L → L.IsSelfInter a → Dense {x : X | IsAlgPt x ∧ ∃ b, IsPtHt L x b ∧ b ≤ e} → a ≤ ((D : ℝ) + 1) * e * gdeg L D := by
  first | exact @GlobalTheory.DenseHt.selfInter_le_of_dense | exact GlobalTheory.DenseHt.selfInter_le_of_dense | (intros; apply GlobalTheory.DenseHt.selfInter_le_of_dense <;> assumption)
