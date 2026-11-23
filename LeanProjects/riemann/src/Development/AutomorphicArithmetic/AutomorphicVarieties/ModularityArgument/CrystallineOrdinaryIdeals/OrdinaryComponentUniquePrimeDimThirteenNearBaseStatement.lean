import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryComponentUniquePrimeDimThirteenNearBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinaryComponent_unique_prime_dim_thirteen_near_base : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ), GlobalTheory.OrdLoc.primesAt0 D U = {GlobalTheory.OrdLoc.It D U} ∧ (GlobalTheory.OrdLoc.It D U).IsPrime ∧ (l : U.R) ∉ GlobalTheory.OrdLoc.It D U ∧ GlobalTheory.OrdLoc.Icr D U ≤ GlobalTheory.OrdLoc.It D U ∧ ringKrullDim (GlobalTheory.OrdLoc.Rt D U) = 13 ∧ GlobalTheory.OrdLoc.On D U (r0 D.η D.Ψ) ∧ ∀ x, IsBase D.η D.Ψ U.r.hom x → ∃ y, x y ≠ 0 ∧ ∀ a ∈ GlobalTheory.OrdLoc.It D U, y * a ∈ GlobalTheory.OrdLoc.Icr D U := by
  first | exact @GlobalTheory.OrdLoc.component_basic | exact GlobalTheory.OrdLoc.component_basic | (intros; apply GlobalTheory.OrdLoc.component_basic <;> assumption)
