import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpaceOfIsConnected
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_lift_of_etale_surjective : ∀ (K : Type) [Field K] [IsAlgClosed K] (X Y : Scheme.{0}) (π : Y ⟶ X), Etale π → Surjective π → ∀ x : Sp K ⟶ X, ∃ y : Sp K ⟶ Y, y ≫ π = x := by
  intro K _ _ X Y π hE hS x
  haveI := hE
  haveI := hS
  have : LocallyOfFiniteType π := inferInstance
  let t : Sp K := IsLocalRing.closedPoint K
  obtain ⟨w, hw⟩ := π.surjective (x t)
  obtain ⟨y, -, -⟩ := Scheme.Pullback.exists_preimage_pullback w t hw
  have : JacobsonSpace ↥(pullback π x) := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨y', -, hy'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback π x)))
    ⟨y, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {y'} := hy'
  refine ⟨pointOfClosedPoint (pullback.snd π x) y' hc ≫ pullback.fst π x, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

end GlobalTheory
