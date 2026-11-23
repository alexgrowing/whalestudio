import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionRepresentableFiniteEtale
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_representable_finite_etale : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => IsAbelianScheme ((Over.pullback W.ι).obj t.G) ∧ TorsFiniteFlat t.G W k ∧ ∃ (Z : Over W.toScheme) (n : overW W Z ⟶ t.G), FinFlatEt Z ∧ n ^ k = 1 ∧ ∀ (T : Over W.toScheme) (x : overW W T ⟶ t.G), x ^ k = 1 → ∃! h : T ⟶ Z, (Over.map W.ι).map h ≫ n = x := by
  first | exact @GlobalTheory.TorsOverOpen.torsion_finFlatEt | exact GlobalTheory.TorsOverOpen.torsion_finFlatEt | (intros; apply GlobalTheory.TorsOverOpen.torsion_finFlatEt <;> assumption)
