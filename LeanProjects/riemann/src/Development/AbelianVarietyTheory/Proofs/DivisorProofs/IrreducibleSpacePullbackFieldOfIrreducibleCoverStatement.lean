import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpacePullbackFieldOfIrreducibleCover
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleSpace_pullback_field_of_irreducible_cover : ∀ {F : Type} [Field F] {X : Scheme.{0}} (h : X ⟶ Sp F) (k : Type) [Field k] (f : F →+* k) (U : X.Opens),
    IsIrreducible (U : Set X) →
    (∀ y ∈ U, ∃ V : X.Opens, V ≤ U ∧ y ∈ V ∧ IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f))) →
    IrreducibleSpace ↑(pullback (U.ι ≫ h) (spMap f)) := by
  first | exact @GlobalTheory.irreducibleSpace_pullback_of_cover | exact GlobalTheory.irreducibleSpace_pullback_of_cover | (intros; apply GlobalTheory.irreducibleSpace_pullback_of_cover <;> assumption)
