import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsThetaPtDown
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaPt_pow_of_isThetaPt_mul : Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (n m : ℕ) (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → Γ((baseOver (Sp K)).left, ⊤)), (∀ i, (x i ^ n) ^ m ^ 2 = 1) → IsThetaPt P (n * m) x v → IsThetaPt P m (fun i => x i ^ n) v := by
  first | exact @GlobalTheory.ThetaNest.isThetaPt_down | exact GlobalTheory.ThetaNest.isThetaPt_down | (intros; apply GlobalTheory.ThetaNest.isThetaPt_down <;> assumption)
