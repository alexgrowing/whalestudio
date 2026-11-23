import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralEqOrderSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_eq_order_sum : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 → ∀ σ : k →+* ℂ, Nonempty (AnRead p σ 1) → ∀ (L : LB X) (φ : Weight p σ L), φ.IsCInf → ∀ s : L.Sec, genericPoint X ∈ nonzeroLocus s → φ.chernInt 1 Set.univ (fun _ => 1) = ∑ᶠ y : CxPts p σ, (secOrd φ.isLB s y.pt : ℝ) := by
  first | exact @GlobalTheory.chernInt_curve_eq_finsum_secOrd | exact GlobalTheory.chernInt_curve_eq_finsum_secOrd | (intros; apply GlobalTheory.chernInt_curve_eq_finsum_secOrd <;> assumption)
