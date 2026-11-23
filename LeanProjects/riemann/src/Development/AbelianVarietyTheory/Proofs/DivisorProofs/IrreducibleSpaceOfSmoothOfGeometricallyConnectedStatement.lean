import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothOfGeometricallyConnected
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleSpace_of_smooth_geometricallyConnected_domain : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))), Smooth G.hom → GeometricallyConnected G.hom → Nonempty G.left → IrreducibleSpace G.left := by
  first | exact @GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain | exact GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain | (intros; apply GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain <;> assumption)
