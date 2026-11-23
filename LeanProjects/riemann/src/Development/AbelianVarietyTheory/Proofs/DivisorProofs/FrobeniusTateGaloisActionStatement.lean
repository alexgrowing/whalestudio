import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusTateGaloisAction
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_tate_galois_action : ∀ (K : Type) [Field K] [Fintype K] (l : ℕ) [Fact l.Prime] (A : AbVar K), tend l A (frob A) = galT l A (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) ∧ vend l A (toEnd0 A (frob A)) = galV l A (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) := by
  first | exact @GlobalTheory.AV.AbVar.frob_tate | exact GlobalTheory.AV.AbVar.frob_tate | (intros; apply GlobalTheory.AV.AbVar.frob_tate <;> assumption)
