import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_pt_of_pt_ext : ∀ (H Q : Scheme.{0}) (φ : H ⟶ Q), LocallyOfFiniteType φ → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (ν : Sp Ω ⟶ Q) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω') (q : Sp Ω' ⟶ H), q ≫ φ = spMap io ≫ ν →
    ∃ p : Sp Ω ⟶ H, p ≫ φ = ν := by
  intro H Q φ hφ Ω _ _ ν Ω' _ io q hq
  have : JacobsonSpace ↥(pullback φ ν) := LocallyOfFiniteType.jacobsonSpace (pullback.snd φ ν)
  have hne : (Set.univ : Set ↥(pullback φ ν)).Nonempty :=
    ⟨pullback.lift q (spMap io) hq (IsLocalRing.closedPoint Ω'), trivial⟩
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints hne isOpen_univ.isLocallyClosed
  have hc' : IsClosed ({c} : Set ↥(pullback φ ν)) := hc
  refine ⟨pointOfClosedPoint (pullback.snd φ ν) c hc' ≫ pullback.fst φ ν, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

end GlobalTheory.Mum
