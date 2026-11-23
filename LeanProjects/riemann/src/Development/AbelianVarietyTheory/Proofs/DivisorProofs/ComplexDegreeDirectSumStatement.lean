import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexDegreeDirectSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProd
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits MonoidalCategory CartesianMonoidalCategory GlobalTheory.VB
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_degree_direct_sum : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsArithVar p 1 → ∀ (E F : S.Modules) (r s : ℕ), VB.IsVB E r → VB.IsVB F s → cxDeg p (E ⊞ F) (r + s) = cxDeg p E r + cxDeg p F s := by
  first | exact @GlobalTheory.CxDegSum.cxDeg_biprod | exact GlobalTheory.CxDegSum.cxDeg_biprod | (intros; apply GlobalTheory.CxDegSum.cxDeg_biprod <;> assumption)
