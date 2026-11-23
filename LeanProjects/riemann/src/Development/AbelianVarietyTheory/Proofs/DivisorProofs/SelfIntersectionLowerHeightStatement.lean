import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolHomog
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_intersection_lower_height : GlobalTheory.Published.VolNef → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (a e : ℝ), L.SemiPos D → NefFib L → L.IsSelfInter a → (∀ x, IsAlgPt x → ∃ b, IsPtHt L x b ∧ e ≤ b) → ((D : ℝ) + 1) * e * gdeg L D ≤ a := by
  first | exact @GlobalTheory.HtSelfInter.selfInter_ge_of_height_ge | exact GlobalTheory.HtSelfInter.selfInter_ge_of_height_ge | (intros; apply GlobalTheory.HtSelfInter.selfInter_ge_of_height_ge <;> assumption)
