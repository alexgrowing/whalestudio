import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartImagePullback
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_part_image_pullback : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ y N p₀, PairRep ψW k y N p₀ → ∃ u : genPart (overW W N) ⟶ t.G, u ^ k = 1 ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ (genPart (overW W N)).left), OverGen F (genPart (overW W N)) x → ∀ q : QkPt P.D.toPre F k, QkPtW.IsPullF F (x ≫ (genι (overW W N)).left) p₀ q → IsImage P F k q (x ≫ u.left) := by
  first | exact @GlobalTheory.GenTorsMap.exists_genericMap | exact GlobalTheory.GenTorsMap.exists_genericMap | (intros; apply GlobalTheory.GenTorsMap.exists_genericMap <;> assumption)
