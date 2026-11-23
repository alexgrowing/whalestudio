import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolHomog
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_section_height_lower_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (m : ℕ) (c b : ℝ) (x : X) (s : ((L.shift (fun _ => -c) fun _ => rfl).pow m).B.Sec), 1 ≤ m → s ∈ ((L.shift (fun _ => -c) fun _ => rfl).pow m).smallSec → x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s → IsAlgPt x → IsPtHt L x b → c ≤ b := by
  first | exact @GlobalTheory.SmallSecHeight.le_ptHt | exact GlobalTheory.SmallSecHeight.le_ptHt | (intros; apply GlobalTheory.SmallSecHeight.le_ptHt <;> assumption)
