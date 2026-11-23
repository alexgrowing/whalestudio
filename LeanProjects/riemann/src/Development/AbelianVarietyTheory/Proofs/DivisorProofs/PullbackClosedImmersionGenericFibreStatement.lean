import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackClosedImmersionGenericFibre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_closed_immersion_generic_fibre : ∀ {W U : Scheme.{0}} [IsIntegral W] {j : U ⟶ W}, GlobalTheory.IsGenericPointHom j → ∀ {A B : Over W} (u : A ⟶ B) {A' B' : Over U} {a : A'.left ⟶ A.left} {b : B'.left ⟶ B.left} (v : A' ⟶ B'), IsPullback a A'.hom A.hom j → IsPullback b B'.hom B.hom j → v.left ≫ b = a ≫ u.left → IsClosedImmersion v.left → ∀ (k : Type) [Field k] (g : Sp k ⟶ W), g (IsLocalRing.closedPoint k) = genericPoint W → IsClosedImmersion ((Over.pullback g).map u).left := by
  first | exact @GlobalTheory.isClosedImmersion_pullback_map_of_genericPoint | exact GlobalTheory.isClosedImmersion_pullback_map_of_genericPoint | (intros; apply GlobalTheory.isClosedImmersion_pullback_map_of_genericPoint <;> assumption)
