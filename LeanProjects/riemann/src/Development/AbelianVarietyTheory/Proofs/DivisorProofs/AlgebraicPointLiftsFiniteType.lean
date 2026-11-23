import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CovLift

theorem exists_lift_of_locallyOfFiniteType : ∀ (V Y : Scheme.{0}) (π : V ⟶ Y), LocallyOfFiniteType π → ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ Y) (u : V), π u = y (IsLocalRing.closedPoint K) → ∃ w : Sp K ⟶ V, w ≫ π = y := by
  intro V Y π hπ K _ _ y u hu
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := y) u (IsLocalRing.closedPoint K) hu
  have : JacobsonSpace ↥(pullback π y : Scheme.{0}) := LocallyOfFiniteType.jacobsonSpace (pullback.snd π y)
  obtain ⟨c, -, hc'⟩ := nonempty_inter_closedPoints (X := ↥(pullback π y : Scheme.{0})) (Z := Set.univ) ⟨z, trivial⟩
    isOpen_univ.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π y) c hc ≫ pullback.fst π y, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

end GlobalTheory.CovLift
